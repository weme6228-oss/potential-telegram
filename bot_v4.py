# -*- coding: utf-8 -*-
"""
دستیار هوشمند - ربات جامع فال، تاروت، سرگرمی و مدیریت گروه تلگرام - نسخه ۵
====================================================================
تغییرات نسبت به نسخه ۴:
  ✅ تغییر نام و هویت بصری: از «فال و سرگرمی» به «دستیار هوشمند» — منوها،
     پیام خوش‌آمد و متن‌های راهنما به‌روزرسانی شد تا یه دستیار حرفه‌ای و
     یکپارچه حس بشه، نه یه ربات ساده‌ی فال.
  ✅ منبع واقعی و آنلاین برای تاروت: هر بار تلاش می‌کنه یه کارت واقعی از
     سایت رایگان tarotapi.dev بگیره (بدون نیاز به کلید API)، و اگه در دسترس
     نبود، خودکار و بی‌صدا میره سراغ موتور کاملاً آفلاینِ داخلی خودش.
  ✅ تنوع فال/تاروت چند برابر شد: به‌جای چند جمله‌ی ثابت، یه موتور ترکیبی
     (opener + حوزه‌ی زندگی + توصیه + رنگ/عدد شانس) هزاران حالت متفاوت
     می‌سازه، و هر ۵۶ کارت کوچک تاروت هم معنی مستقل و معنادار خودشون رو دارن
     (نه یه جمله‌ی تکراری برای کل یه دسته).
  ✅ «هوشمندی» بدون سرویس پولی: چون از Gemini/OpenRouter استفاده نمی‌کنیم،
     یه موتور پاسخ‌گویی قانون‌محورِ آفلاین اضافه شد که وقتی کسی مستقیم با
     ربات حرف بزنه (اسمشو بیاره یا ریپلاش کنه) جواب طبیعی و مرتبط می‌ده.
  ✅ حذف قابلیت‌های غیرفعال/گمراه‌کننده: دستور /translate که دیگه کار
     نمی‌کرد (چون به سرویس هوش مصنوعی نیاز داشت) کامل حذف شد.
  ✅ رفع باگ چند تابعِ تکراری (generate_fal دوبار تعریف شده بود) و پاکسازی
     کدهای مرده‌ی مرتبط با سرویس‌های هوش مصنوعیِ حذف‌شده.

نصب پیش‌نیازها:
    pip install "python-telegram-bot[job-queue]" requests

قبل از اجرا، این متغیر محیطی رو تنظیم کن (توکن رو هاردکد نکن!):
    export BOT_TOKEN="توکن ربات از BotFather"

اجرا:
    python bot_v4.py
"""

import os
import re
import html
import json
import time
import random
import asyncio
import logging
import unicodedata
import traceback
from pathlib import Path
from datetime import datetime, timedelta
from collections import defaultdict, deque

import requests
from telegram import Update, BotCommand, InlineKeyboardButton, InlineKeyboardMarkup, ChatPermissions
from telegram.ext import (
    ApplicationBuilder,
    CommandHandler,
    MessageHandler,
    CallbackQueryHandler,
    ContextTypes,
    filters,
)
from telegram.error import BadRequest, TelegramError, Forbidden

# ============================================================
# تنظیمات اصلی — از متغیرهای محیطی خونده می‌شه، هرگز داخل کد ننویس
# ============================================================
BOT_TOKEN = os.environ.get("BOT_TOKEN", "").strip()

DATA_DIR = Path(__file__).parent
BAD_WORDS_FILE = DATA_DIR / "bad_words.json"
# فضای ذخیره‌سازی جداگانه‌ی روی سرور، مخصوص کلماتی که ادمین‌ها از توی خودِ ربات
# (با دکمه‌ی شیشه‌ای پنل مدیریت) اضافه می‌کنن. این فایل کاملاً جدا از لیست پیش‌فرضه
# تا هیچ‌وقت با آپدیت لیست پیش‌فرض قاطی/بازنویسی نشه.
CUSTOM_BAD_WORDS_FILE = DATA_DIR / "bad_words_custom.json"
WARN_FILE = DATA_DIR / "warns.json"
# فضای ذخیره‌سازی وضعیت یادآور زمان‌بندی‌شده (فعال/غیرفعال) به ازای هر گروه
REMINDER_FILE = DATA_DIR / "reminder_state.json"

logging.basicConfig(
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    level=logging.INFO,
)
logger = logging.getLogger(__name__)

_http_session = requests.Session()
_http_session.headers.update({"User-Agent": "Mozilla/5.0 (compatible; FalBot/1.0)"})

PRICE_CACHE = {"data": None, "time": None}
CACHE_SECONDS = 90

FLOOD_WINDOW = 10
FLOOD_LIMIT = 5
user_message_times = defaultdict(lambda: deque(maxlen=FLOOD_LIMIT))

# قفل ساده‌ی نوشتن فایل، تا اگه دو تا کاربر همزمان کلمه اضافه کردن، فایل خراب/overwrite نشه
_file_write_lock = asyncio.Lock()

# ============================================================
# لیست کلمات نامناسب (پیش‌فرض)
# ============================================================
DEFAULT_BAD_WORDS_FA = [
    "کصکش", "کصکشش", "کیری", "کیر", "جنده", "کونی", "کون",
    "لاشی", "عوضی", "حرومزاده", "مادرجنده", "خارکسه", "گاییدم",
    "کسکش", "ننتو", "زنیکه", "کثافت", "جاکش", "عنتر",
    "کصکش", "کسکش", "گائیدم", "گاییدنت", "بگا", "بگایی",
    "خایه", "تخم سگ", "حروم‌زاده", "مادرقحبه", "قحبه", "منگل",
    "عقب‌مونده", "احمق جان", "کره خر", "خر کثیف", "آشغال عوضی",
    "بی‌ناموس", "بی ناموس", "ناموس نداری", "پدرسگ", "سگ پدر",
    "کیرم", "کیرتو", "کونده", "کونی خان", "خایمال", "چاقال",
    "بی‌شرف", "هرزه", "فاحشه", "دیوث", "قرمساق", "لجن", "لاشخور",
]
DEFAULT_BAD_WORDS_EN = [
    "fuck", "fucking", "fucker", "fck", "shit", "bullshit", "bitch",
    "asshole", "bastard", "cunt", "dick", "dickhead", "pussy", "whore",
    "slut", "motherfucker", "retard", "faggot", "nigger", "cock",
    "wanker", "twat", "douchebag", "piece of shit", "jackass",
]

LEET_MAP = {"0": "o", "1": "i", "3": "e", "4": "a", "5": "s", "7": "t", "@": "a", "$": "s", "!": "i"}


def load_json_safe(path: Path, default):
    if path.exists():
        try:
            with open(path, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception as e:
            logger.warning(f"خطا در خواندن {path}: {e}")
    return default


def save_json_safe(path: Path, data):
    try:
        with open(path, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
    except Exception as e:
        logger.warning(f"خطا در ذخیره {path}: {e}")


bad_data = load_json_safe(BAD_WORDS_FILE, {"fa": DEFAULT_BAD_WORDS_FA, "en": DEFAULT_BAD_WORDS_EN})
BAD_WORDS_FA = bad_data.get("fa", DEFAULT_BAD_WORDS_FA)
BAD_WORDS_EN = bad_data.get("en", DEFAULT_BAD_WORDS_EN)
if not BAD_WORDS_FILE.exists():
    save_json_safe(BAD_WORDS_FILE, {"fa": BAD_WORDS_FA, "en": BAD_WORDS_EN})

# ساختار فایل سفارشی: {"<chat_id>": ["کلمه۱", "کلمه۲", ...], ...}
# هر گروه لیست کلمات سفارشی خودش رو داره، تا کلمه‌ای که یک ادمین توی یک گروه اضافه
# می‌کنه، توی گروه‌های دیگه اعمال نشه (مگر اینکه بخوای سراسری باشه - قابل تغییره).
custom_bad_words = load_json_safe(CUSTOM_BAD_WORDS_FILE, {})
if not CUSTOM_BAD_WORDS_FILE.exists():
    save_json_safe(CUSTOM_BAD_WORDS_FILE, custom_bad_words)

warns_data = load_json_safe(WARN_FILE, {})  # {"chat_id:user_id": count}

# وضعیت یادآور: {"<chat_id>": true/false}
reminder_enabled = load_json_safe(REMINDER_FILE, {})
if not REMINDER_FILE.exists():
    save_json_safe(REMINDER_FILE, reminder_enabled)
# جلوگیری از ارسال تکراری در یک ساعت مشخص (in-memory، نیازی به دیسک نداره)
reminder_last_sent_hour = {}

# کاربرانی که الان توی «حالت افزودن کلمه نامناسب» هستن: {user_id: chat_id}
pending_badword_add = {}

REMINDER_EVEN_TEXT = "🔔 دینگ دینگ! وقت پاچیدن چاهه 🕳️"
REMINDER_ODD_TEXT = "🔔 دینگ دینگ! بدو که شام ننه‌جون سرد شد 🍽️"


def normalize_text(text: str) -> str:
    text = text.lower()
    text = unicodedata.normalize("NFKC", text)
    text = "".join(LEET_MAP.get(ch, ch) for ch in text)
    text = re.sub(r"[\s\.\-_\*]+", "", text)
    text = re.sub(r"(.)\1{1,}", r"\1", text)
    return text


def get_custom_words_for_chat(chat_id) -> list:
    return custom_bad_words.get(str(chat_id), [])


def contains_bad_word(text: str, chat_id=None):
    """چک می‌کنه که متن شامل ناسزا هست یا نه - هم لیست پیش‌فرض هم لیست سفارشی همون گروه."""
    norm = normalize_text(text)
    all_words = BAD_WORDS_FA + BAD_WORDS_EN
    if chat_id is not None:
        all_words = all_words + get_custom_words_for_chat(chat_id)
    for w in [normalize_text(w) for w in all_words]:
        if w and w in norm:
            return True
    return False


async def is_admin(update: Update, context: ContextTypes.DEFAULT_TYPE) -> bool:
    chat = update.effective_chat
    user = update.effective_user
    if chat.type == "private":
        return True
    try:
        member = await context.bot.get_chat_member(chat.id, user.id)
        return member.status in ("administrator", "creator")
    except Exception:
        return False


def mention_html(user) -> str:
    name = html.escape(user.first_name or "کاربر")
    return f'<a href="tg://user?id={user.id}">{name}</a>'


# ============================================================
# 🧠 «هوشمندی» بدون نیاز به سرویس هوش مصنوعی پولی
# چون از سرویس‌های پولی هوش مصنوعی (Gemini/OpenRouter) استفاده نمی‌کنیم، به‌جاش
# دو موتور جایگزین ساختیم که کاملاً آفلاین، رایگان و سریع کار می‌کنن:
#   ۱) موتور تولید ترکیبی (فال/تاروت): قطعات مختلف متن رو تصادفی و هوشمندانه
#      کنار هم می‌چینه؛ نتیجه هزاران حالت متفاوت ممکنه، نه چند جمله‌ی تکراری.
#   ۲) دستیار مکالمه‌ی قانون‌محور (زیر همین بخش): وقتی کسی مستقیم با ربات
#      حرف بزنه، هم تشخیص نیت (Intent) با دقت بیشتر انجام می‌ده، هم برای
#      سؤالاتی مثل ساعت/تاریخ، محاسبه‌ی واقعی و دقیق (نه متن ثابت) برمی‌گردونه.
# ============================================================

# ------------------------------------------------------------
# 📅 تبدیل دقیق میلادی به شمسی - محاسبه‌ی واقعی، بدون نیاز به کتابخانه‌ی جانبی
# (الگوریتم استاندارد تقویم جلالی؛ برای پاسخ «امروز چندمه؟» استفاده می‌شه)
# ------------------------------------------------------------
def gregorian_to_jalali(gy: int, gm: int, gd: int):
    g_days_in_month = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
    j_days_in_month = [31, 31, 31, 31, 31, 31, 30, 30, 30, 30, 30, 29]
    gy2 = gy - 1600
    gm2 = gm - 1
    gd2 = gd - 1
    g_day_no = 365 * gy2 + (gy2 + 3) // 4 - (gy2 + 99) // 100 + (gy2 + 399) // 400
    for i in range(gm2):
        g_day_no += g_days_in_month[i]
    if gm2 > 1 and ((gy % 4 == 0 and gy % 100 != 0) or (gy % 400 == 0)):
        g_day_no += 1
    g_day_no += gd2
    j_day_no = g_day_no - 79
    j_np = j_day_no // 12053
    j_day_no %= 12053
    jy = 979 + 33 * j_np + 4 * (j_day_no // 1461)
    j_day_no %= 1461
    if j_day_no >= 366:
        jy += (j_day_no - 1) // 365
        j_day_no = (j_day_no - 1) % 365
    jm, jd = 12, j_day_no + 1
    for i in range(11):
        if j_day_no < j_days_in_month[i]:
            jm, jd = i + 1, j_day_no + 1
            break
        j_day_no -= j_days_in_month[i]
    return jy, jm, jd


PERSIAN_MONTHS = [
    "فروردین", "اردیبهشت", "خرداد", "تیر", "مرداد", "شهریور",
    "مهر", "آبان", "آذر", "دی", "بهمن", "اسفند",
]
PERSIAN_WEEKDAYS = {5: "شنبه", 6: "یک‌شنبه", 0: "دوشنبه", 1: "سه‌شنبه", 2: "چهارشنبه", 3: "پنج‌شنبه", 4: "جمعه"}


def get_persian_datetime_text() -> str:
    now = datetime.now()
    jy, jm, jd = gregorian_to_jalali(now.year, now.month, now.day)
    weekday = PERSIAN_WEEKDAYS[now.weekday()]
    return (
        f"📅 امروز {weekday}، {jd} {PERSIAN_MONTHS[jm - 1]} {jy} هست "
        f"(برابر با {now.strftime('%Y-%m-%d')} میلادی).\n"
        f"🕒 ساعت دقیق سرور الان: {now.strftime('%H:%M:%S')}"
    )


def get_time_text() -> str:
    now = datetime.now()
    return f"🕒 ساعت دقیق الان: {now.strftime('%H:%M:%S')}"


# ------------------------------------------------------------
# 💬 دستیار مکالمه‌ی قانون‌محور (Rule-Based Intent Matching) - کاملاً آفلاین
# نسخه‌ی حرفه‌ای: نرمال‌سازی دقیق‌تر متن ورودی + دسته‌بندی گسترده‌تر نیت‌ها +
# واژگان متنوع‌تر و رسمی‌تر + پاسخ‌های محاسباتی واقعی (ساعت/تاریخ شمسی).
# فقط وقتی فعال می‌شه که پیام مستقیماً خطاب به رباته (اسمش بیاد یا ریپلای
# روی پیام خودش باشه)، تا مزاحم گفت‌وگوی عادی گروه نشه.
# ------------------------------------------------------------
_SMART_PUNCT_RE = re.compile(r"[؟?!.,،:؛;\-_]+")


def _smart_normalize(text: str) -> str:
    """متن رو برای تشخیص نیت آماده می‌کنه: کوچک، بدون علائم نگارشی، فاصله‌های
    تکراری یکی می‌شن - ولی برخلاف normalize_text (مخصوص فیلتر ناسزا)، فاصله‌ی
    بین کلمات حفظ می‌شه تا عبارت‌های چندکلمه‌ای («کی هستی») درست تشخیص داده بشن."""
    t = text.strip().lower()
    t = unicodedata.normalize("NFKC", t)
    t = _SMART_PUNCT_RE.sub(" ", t)
    t = re.sub(r"\s+", " ", t).strip()
    return t


# هر دسته: (نام دسته، لیست کلیدواژه/عبارت، لیست پاسخ‌های متنوع و حرفه‌ای)
SMART_REPLY_RULES = [
    ("greeting",
     ["سلام", "درود", "هلو", "hi", "hello", "سلاام", "علیک"],
     ["سلام {name} عزیز! خوش اومدی، در خدمتتم. 😊",
      "درود بر {name}! من دستیار هوشمند این گروهم؛ برای دیدن امکاناتم دستور /start رو بزن.",
      "سلام! خوشحالم که بهم پیام دادی. چطور می‌تونم کمکت کنم؟",
      "علیک سلام {name} جان! امروز چه کمکی از دستم برمیاد؟"]),
    ("wellbeing",
     ["چطوری", "خوبی", "حالت چطوره", "چه حالی داری", "خسته نباشی"],
     ["ممنونم، همیشه آماده و سرحالم! تو چطوری {name} جان؟",
      "عالی‌ام، مرسی که پرسیدی. آماده‌ی کمک به توام؛ چی لازم داری؟",
      "همیشه در بهترین حالت کاری‌ام، چون آفلاین و بدون وقفه فعالم! 😄"]),
    ("identity",
     ["اسمت چیه", "کی هستی", "معرفی کن", "تو کی هستی", "چی هستی", "خودتو معرفی کن"],
     ["من «دستیار هوشمند» این گروهم؛ امکاناتی مثل فال و تاروت با منبع آنلاین واقعی، "
      "بازی گروهی گرگینه، مدیریت و نظم‌دهی گروه و یادآورهای زمان‌بندی‌شده دارم. با /start شروع کن.",
      "من دستیار هوشمند و چندمنظوره‌ی این گروهم 🤖 — از فال و تاروت گرفته تا مدیریت کامل گروه و بازی گروهی، همه‌چی دارم.",
      "اسمم دستیار هوشمنده! برای دیدن فهرست کامل امکاناتم /start رو بزن."]),
    ("creator",
     ["کی ساختت", "سازنده ات کیه", "سازندت کیه", "کی درستت کرد", "برنامه نویست کیه", "مالکت کیه"],
     ["منو ادمین‌های همین گروه راه‌اندازی و پیکربندی کردن؛ در خدمت شما و اعضای گروهم.",
      "یه توسعه‌دهنده‌ی مستقل منو برای این گروه طراحی و تنظیم کرده."]),
    ("real_ai_question",
     ["هوش مصنوعی هستی", "واقعا هوشمندی", "ربات واقعی هستی", "chatgpt هستی", "جیپیتی هستی"],
     ["به‌طور دقیق، من یه دستیار قانون‌محورِ آفلاینم؛ نیت پیامت رو تشخیص می‌دم و بر اساس اون جواب می‌دم - "
      "به یه مدل زبانی بزرگ متصل نیستم، ولی برای فال، تاروت، مدیریت گروه و محاسبات دقیق (مثل ساعت و تاریخ) کاملاً قابل اتکام.",
      "من از یه موتور تشخیص‌الگوی هوشمند و آفلاین استفاده می‌کنم، نه یه سرویس هوش مصنوعیِ متصل به اینترنت. "
      "همینم باعث می‌شه سریع، رایگان و همیشه در دسترس باشم."]),
    ("capabilities",
     ["کمک", "راهنما", "چیکار بلدی", "چه کاری بلدی", "چه امکاناتی داری", "چیکارا میکنی"],
     ["برای دیدن فهرست کامل امکاناتم دستور /start رو بزن؛ یه منوی کامل و دسته‌بندی‌شده براش طراحی شده.",
      "من فال، تاروت (با منبع آنلاین واقعی)، فال حافظ، بازی گروهی گرگینه، مدیریت و نظم‌دهی گروه، "
      "یادآور زمان‌بندی‌شده و چند سرگرمی دیگه هم دارم. با /start شروع کن.",
      "امکانات من رو می‌تونی از منوی /start ببینی؛ هم ابزارهای سرگرمی دارم هم ابزارهای مدیریتیِ حرفه‌ای."]),
    ("time_query",
     ["ساعت چنده", "ساعت چند شد", "الان ساعت چنده", "ساعت چنده الان"],
     []),  # پاسخ به‌صورت پویا و محاسبه‌شده تولید می‌شه، نه از این لیست
    ("date_query",
     ["امروز چندمه", "تاریخ امروز", "چه روزیه امروز", "چندمه امروز", "امروز چه روزیه"],
     []),  # پاسخ به‌صورت پویا و محاسبه‌شده تولید می‌شه، نه از این لیست
    ("boredom",
     ["حوصلم سررفته", "خسته شدم", "بی‌حوصله‌ام", "چیکار کنیم", "حوصله ندارم"],
     ["پیشنهاد می‌کنم یه سر به /wheel (چرخ شانس) یا /td (جرأت یا حقیقت) بزنی - حسابی سرگرمت می‌کنه!",
      "برای رفع بی‌حوصلگی، /joke یا /tarot رو امتحان کن؛ یا بازی گروهی /gorgineh رو راه بنداز."]),
    ("frustration",
     ["بلد نیستی", "کار نمیکنی", "خرابی", "بی‌فایده‌ای", "به درد نمیخوری", "بی مصرفی"],
     ["ببخشید اگه انتظارت رو برآورده نکردم؛ می‌تونی از /start همه‌ی امکاناتم رو دقیق ببینی و امتحان کنی.",
      "متوجه‌ام که شاید دقیقاً چیزی که می‌خواستی نبود؛ برای فهرست کامل و دقیق دستوراتم /start رو بزن."]),
    ("thanks",
     ["ممنون", "مرسی", "دمت گرم", "تشکر", "سپاس"],
     ["خواهش می‌کنم {name} عزیز! هر وقت لازم داشتی در خدمتم. 🙌",
      "قابل شما رو نداشت! خوشحال می‌شم بازم کمک کنم.",
      "سپاس از شما {name} جان، همیشه آماده‌ی کمکم."]),
    ("affection",
     ["دوستت دارم", "عاشقتم", "خیلی خفنی", "محشری"],
     ["لطف داری {name} جان! از اینکه بهت کمک می‌کنم خیلی خوشحالم. 😊",
      "ممنون از محبتت! سعی می‌کنم همیشه بهترین دستیار برای این گروه باشم."]),
    ("farewell",
     ["خداحافظ", "بای", "فعلا", "می‌رم", "خدافظ"],
     ["خداحافظ {name} جان، هر وقت لازم داشتی صدام کن! 👋",
      "به امید دیدار! من همیشه اینجا و آماده‌ام."]),
]


def smart_rule_based_reply(text: str, name: str) -> "str | None":
    norm = _smart_normalize(text)

    # دسته‌های «پویا» که پاسخ‌شون واقعاً محاسبه می‌شه (نه متن ثابت) - اول چک می‌شن
    DYNAMIC_HANDLERS = {
        "time_query": lambda: get_time_text(),
        "date_query": lambda: get_persian_datetime_text(),
    }

    for label, keywords, responses in SMART_REPLY_RULES:
        if not any(kw in norm for kw in keywords):
            continue
        if label in DYNAMIC_HANDLERS:
            return DYNAMIC_HANDLERS[label]()
        return random.choice(responses).format(name=name)

    # هیچ الگویی match نشد - یه جواب عمومی، حرفه‌ای و راهنما
    return random.choice([
        f"متوجه نشدم دقیقاً منظورت چیه {name} جان؛ برای دیدن فهرست کامل امکاناتم /start رو بزن.",
        "این مورد رو هنوز نمی‌شناسم، ولی با /start می‌تونی همه‌ی چیزهایی که بلدم رو ببینی.",
        "درخواستت رو دقیق تشخیص ندادم؛ اگه دنبال فال، تاروت، بازی یا مدیریت گروهی، از /start شروع کن.",
    ])


# ============================================================
# آرکانای بزرگ (۲۲ کارت) و کوچک (۵۶ کارت)
# ============================================================
MAJOR_ARCANA = [
    ("دلقک", "The Fool", "شروع تازه، ماجراجویی و اعتماد به مسیر جدید."),
    ("جادوگر", "The Magician", "قدرت اراده، مهارت و به‌کارگیری استعدادها."),
    ("کاهنه", "The High Priestess", "شهود، رازها و دانش پنهان."),
    ("امپراتریس", "The Empress", "فراوانی، خلاقیت و رشد."),
    ("امپراتور", "The Emperor", "نظم، ساختار و کنترل بر شرایط."),
    ("پاپ / خردمند", "The Hierophant", "سنت، آموزش و راهنمایی معنوی."),
    ("عاشقان", "The Lovers", "انتخاب مهم، هماهنگی و رابطه."),
    ("ارابه", "The Chariot", "اراده قوی، پیروزی با تلاش و کنترل."),
    ("قدرت", "Strength", "شجاعت درونی و کنترل احساسات."),
    ("زاهد", "The Hermit", "درون‌نگری، تنهایی سازنده و جست‌وجوی حقیقت."),
    ("چرخ بخت", "Wheel of Fortune", "تغییر ناگهانی سرنوشت، فرصت‌های تازه."),
    ("عدالت", "Justice", "انصاف، حقیقت و پیامدهای اعمال."),
    ("مرد آویزان", "The Hanged Man", "تعلیق، دیدگاه تازه، فداکاری."),
    ("مرگ", "Death", "پایان یک دوره و آغاز تحول بزرگ."),
    ("اعتدال", "Temperance", "تعادل، صبر و ترکیب هماهنگ."),
    ("اهریمن", "The Devil", "وابستگی، محدودیت‌های خودساخته."),
    ("برج", "The Tower", "تغییر ناگهانی و فروریختن باورهای غلط."),
    ("ستاره", "The Star", "امید، الهام و آرامش پس از سختی."),
    ("ماه", "The Moon", "ابهام، ترس‌های پنهان و ناخودآگاه."),
    ("خورشید", "The Sun", "شادی، موفقیت و انرژی مثبت."),
    ("داوری", "Judgement", "بیداری، ارزیابی و تصمیم سرنوشت‌ساز."),
    ("دنیا", "The World", "تکمیل یک دوره، رسیدن به هدف."),
]
MINOR_SUITS = {
    "جام (Cups)": "احساسات، روابط و عشق",
    "پنتاکل (Pentacles)": "مال، کار و مسائل مادی",
    "شمشیر (Swords)": "فکر، چالش و تصمیم‌گیری",
    "چوبدستی (Wands)": "انرژی، خلاقیت و شور",
}
MINOR_RANKS = [
    "آس", "دو", "سه", "چهار", "پنج", "شش", "هفت", "هشت", "نه", "ده",
    "پیک (Page)", "شوالیه (Knight)", "ملکه (Queen)", "شاه (King)",
]

# نیّتِ/انرژیِ هر «رتبه» - برای اینکه معنی کارت‌های کوچک به‌جای یه جمله‌ی
# تکراری («مرتبط با ...»)، هرکدوم شخصیت مستقل و معنادار خودشون رو داشته باشن
RANK_NUANCE_FA = {
    "آس": "یک شروع تازه، خام و پرانرژی؛ بذر یه اتفاق نو که تازه کاشته شده",
    "دو": "یک انتخاب یا توازن مهم بین دو مسیر",
    "سه": "رشد اولیه، همکاری و جوونه زدن نتیجه‌ی تلاش‌های قبلی",
    "چهار": "ثبات، آرامش نسبی و تثبیت شرایط فعلی",
    "پنج": "یک چالش یا کشمکش موقتی که باید ازش عبور کنی",
    "شش": "بازگشت هماهنگی و تعادل بعد از یه دوره‌ی سخت",
    "هفت": "زمان ارزیابی، صبر و بازبینی مسیر",
    "هشت": "تلاش پیوسته، تمرکز و پیشرفت آروم ولی مطمئن",
    "نه": "نزدیک شدن به نتیجه؛ یه قدم تا هدف فاصله داری",
    "ده": "تکمیل یک چرخه و آماده شدن برای فصل بعدی زندگی",
    "پیک (Page)": "یه پیام، خبر یا یادگیری تازه که داره بهت می‌رسه",
    "شوالیه (Knight)": "حرکت، جسارت و یه اقدام جدی که باید انجامش بدی",
    "ملکه (Queen)": "بلوغ درونی، شهود و مدیریت هوشمندانه‌ی احساسات",
    "شاه (King)": "تسلط بیرونی، مسئولیت‌پذیری و تصمیم‌گیری قاطع",
}

TAROT_REVERSED_NOTE = "\n\n(این کارت امروز به‌صورت معکوس اومده، یعنی همین انرژی داره از درون یا با تأخیر خودشو نشون می‌ده.)"

TAROT_ADVICE_CLOSERS = [
    "🔎 جمع‌بندی و توصیه: امروز رو با آرامش جلو برو و به دلت گوش بده.",
    "🔎 جمع‌بندی و توصیه: یه قدم کوچیک ولی مطمئن بردار، نتیجه‌ش رو خیلی زود می‌بینی.",
    "🔎 جمع‌بندی و توصیه: قبل از هر تصمیمی، یه نفس عمیق بکش و دوباره فکر کن.",
    "🔎 جمع‌بندی و توصیه: با کسی که بهش اعتماد داری مشورت کن، دیدگاه تازه‌ای می‌گیری.",
    "🔎 جمع‌بندی و توصیه: امروز روز خوبیه برای شفاف‌سازی یه رابطه یا موضوع نیمه‌کاره.",
    "🔎 جمع‌بندی و توصیه: به‌جای عجله، روی کیفیت کارت تمرکز کن.",
    "🔎 جمع‌بندی و توصیه: یه فرصت کوچیک رو دست‌کم نگیر، می‌تونه شروع چیز بزرگی باشه.",
    "🔎 جمع‌بندی و توصیه: به خودت زمان بده؛ همه‌چی لازم نیست همین امروز حل بشه.",
]

# نگاشت انگلیسی↔فارسی، برای وقتی که یه کارت واقعی از سایت tarotapi.dev گرفته می‌شه
RANK_EN2FA = {
    "ace": "آس", "two": "دو", "three": "سه", "four": "چهار", "five": "پنج",
    "six": "شش", "seven": "هفت", "eight": "هشت", "nine": "نه", "ten": "ده",
    "page": "پیک (Page)", "knight": "شوالیه (Knight)",
    "queen": "ملکه (Queen)", "king": "شاه (King)",
}
SUIT_EN2FA = {
    "cups": "جام (Cups)", "pentacles": "پنتاکل (Pentacles)",
    "swords": "شمشیر (Swords)", "wands": "چوبدستی (Wands)",
}
MAJOR_EN2FA = {en: (fa, meaning) for fa, en, meaning in MAJOR_ARCANA}


def build_full_tarot_deck():
    deck = [(f"{fa} ({en})", meaning) for fa, en, meaning in MAJOR_ARCANA]
    for suit, theme in MINOR_SUITS.items():
        for rank in MINOR_RANKS:
            nuance = RANK_NUANCE_FA.get(rank, "")
            deck.append((f"{rank} {suit}", f"{nuance}، در حوزه‌ی {theme}."))
    return deck


TAROT_DECK_FULL = build_full_tarot_deck()


def map_tarotapi_card_to_persian(name_en: str):
    """اسم کارتی که از سایت واقعی tarotapi.dev گرفته می‌شه رو به معادل فارسیِ
    خودمون توی دک آفلاین نگاشت می‌کنه. اگه نتونه match کنه None برمی‌گردونه
    (و کد صدازننده خودکار می‌ره سراغ یه کارت کاملاً آفلاین)."""
    name_en = (name_en or "").strip().lower()
    if not name_en:
        return None
    # آرکانای بزرگ: اسم دقیقاً باید با یکی از ۲۲ تا برابر باشه
    for en, (fa, meaning) in MAJOR_EN2FA.items():
        if en.lower() == name_en:
            return f"{fa} ({en})", meaning
    # آرکانای کوچک: فرمت رایج API چیزی شبیه "ace of cups" یا "two of wands"
    if " of " in name_en:
        rank_part, suit_part = name_en.split(" of ", 1)
        rank_fa = RANK_EN2FA.get(rank_part.strip())
        suit_fa = SUIT_EN2FA.get(suit_part.strip())
        if rank_fa and suit_fa:
            key = f"{rank_fa} {suit_fa}"
            for deck_name, meaning in TAROT_DECK_FULL:
                if deck_name == key:
                    return deck_name, meaning
    return None


def _fetch_tarot_card_online_blocking():
    """یه کارت واقعی و تصادفی از یه منبع آنلاینِ واقعی (tarotapi.dev - رایگان،
    بدون نیاز به کلید API) می‌گیره. اگه اینترنت/سایت در دسترس نباشه، None
    برمی‌گردونه و کد صدازننده خودکار میره سراغ حالت کاملاً آفلاین."""
    try:
        r = _http_session.get("https://tarotapi.dev/api/v1/cards/random", params={"n": 1}, timeout=6)
        if r.status_code == 200:
            data = r.json()
            cards = data.get("cards", [])
            if cards:
                card = cards[0]
                return {
                    "name_en": card.get("name", ""),
                    "meaning_up": card.get("meaning_up", ""),
                    "meaning_rev": card.get("meaning_rev", ""),
                }
    except Exception as e:
        logger.warning(f"tarotapi.dev fetch failed: {e}")
    return None


FAL_OPENERS = [
    "امروز روز خوبیه برای شروع یه کار جدید.", "امروز حال‌وهوای متفاوتی در انتظارته.",
    "یه اتفاق کوچیک ولی معنادار امروز میفته.", "امروز روزیه که باید به شهودت اعتماد کنی.",
    "انرژی امروزت رو به بالاست، ازش خوب استفاده کن.", "امروز یکم غیرمنتظره پیش می‌ره، ولی به نفعته.",
    "امروز روز آرامشه، لازم نیست عجله کنی.", "یه فرصت کوچیک امروز سر راهت قرار می‌گیره.",
]
FAL_LIFE_AREAS = [
    "توی کار و درس، تمرکزت بیشتر از همیشه جواب می‌ده.",
    "توی روابطت، صداقت امروز بهترین انتخابه.",
    "از نظر مالی، یه خبر یا فرصت کوچیک در راهه.",
    "توی خانواده یا دوستی‌هات، یه گفت‌وگوی مهم پیش میاد.",
    "از نظر احساسی، امروز حس‌های قوی‌تری تجربه می‌کنی.",
    "سلامتیت رو دست‌کم نگیر، بدنت به استراحت نیاز داره.",
    "یه تصمیم قدیمی داره بالاخره جواب می‌ده.",
    "یه دوست یا آشنای قدیمی به یادت می‌افته.",
]
FAL_ADVICE = [
    "فقط حواست باشه عجله نکنی و قدم‌به‌قدم پیش بری. 🌊",
    "ذهنت رو باز نگه دار، همه‌چی همون‌جوری نیست که فکر می‌کنی. 📩",
    "با آرامش و صداقت جلو برو، نتیجه بهتره. 👂",
    "ترست رو کنار بذار و شروع کن، الان بهترین زمانه. 🚀",
    "زودتر قدم اول رو بردار، این ارتباط دوباره جون می‌گیره. 💬",
    "قبل از هر تصمیمی، همه جوانب رو بررسی کن. 💰",
    "به خودت اجازه بده کمی استراحت کنی. ☕",
    "با فکر باز تصمیم بگیر، نه احساسی و ناگهانی. 🧠",
    "چشمات رو باز نگه دار، شاید یه نفر همین نزدیکی‌ها منتظرته. ❤️",
    "یه ریسک حساب‌شده رو امتحان کن؛ می‌تونه جواب بده. 🎲",
]
FAL_LUCKY_COLORS = ["آبی", "قرمز", "سبز", "طلایی", "بنفش", "نارنجی", "سفید", "فیروزه‌ای"]


async def generate_fal(name: str) -> str:
    # موتور ترکیبی: هر بار قطعات مختلف رو تصادفی کنار هم می‌چینه - آفلاین و سریع
    opener = random.choice(FAL_OPENERS)
    area = random.choice(FAL_LIFE_AREAS)
    advice = random.choice(FAL_ADVICE)
    lucky_color = random.choice(FAL_LUCKY_COLORS)
    lucky_number = random.randint(1, 99)
    return (
        f"{opener} {area} {advice}\n\n"
        f"🎨 رنگ شانس امروزت: {lucky_color} | 🔢 عدد شانس: {lucky_number}"
    )


HAFEZ_VERSES = [
    "الا یا ایها الساقی ادر کاسا و ناولها / که عشق آسان نمود اول ولی افتاد مشکل‌ها",
    "بیا تا گل برافشانیم و می در ساغر اندازیم / فلک را سقف بشکافیم و طرحی نو دراندازیم",
    "دوش وقت سحر از غصه نجاتم دادند / وندر آن ظلمت شب آب حیاتم دادند",
    "یوسف گم‌گشته باز آید به کنعان غم مخور / کلبهٔ احزان شود روزی گلستان غم مخور",
    "اگر آن ترک شیرازی به دست آرد دل ما را / به خال هندویش بخشم سمرقند و بخارا را",
    "سال‌ها دل طلب جام جم از ما می‌کرد / وان چه خود داشت ز بیگانه تمنا می‌کرد",
    "صبا به لطف بگو آن غزال رعنا را / که سر به کوه و بیابان تو داده‌ای ما را",
    "بلبلی برگ گلی خوش‌رنگ در منقار داشت / وندر آن برگ و نوا خوش ناله‌های زار داشت",
    "حسن تو همیشه در فزون باد / رویت همه ساله لاله‌گون باد",
    "دل می‌رود ز دستم صاحب‌دلان خدا را / دردا که راز پنهان خواهد شد آشکارا",
    "بنال بلبل اگر با منت سر یاری است / که ما دو عاشق زاریم و کار ما زاری است",
    "مرا می‌بینی و هر دم زیادت می‌کنی دردم / تو را می‌بینم و میلم زیادت می‌شود هر دم",
    "زلف آشفته و خوی‌کرده و خندان‌لب و مست / پیرهن چاک و غزل‌خوان و صراحی در دست",
    "ای پادشه خوبان داد از غم تنهایی / دل بی تو به جان آمد وقت است که بازآیی",
    "گفتم غم تو دارم گفتا غمت سرآید / گفتم که ماه من شو گفتا اگر برآید",
    "روزگاری است که سودای بتان دین من است / غم این کار نشاط دل غمگین من است",
]

PROVERBS_FA = [
    "کار نیکو کردن از پر کردن است؛ هر کاری با تمرین جا می‌افته.",
    "آدمی به فکر نیک، به گفتار نیک، به کردار نیک می‌رسه.",
    "تا نباشد چیزکی، مردم نگویند چیزها.",
    "آب رفته به جوی باز نمی‌گرده، پس قدر لحظه رو بدون.",
    "سنگ بزرگ علامت نزدن است.",
    "کبوتر با کبوتر، باز با باز؛ کند همجنس با همجنس پرواز.",
    "هر که بامش بیش، برفش بیشتر.",
    "دیر رسیدن بهتر از هرگز نرسیدنه.",
    "از کوزه همان برون تراود که در اوست.",
    "با یک گل بهار نمی‌شه؛ صبر و پشتکار کلیده.",
    "آدم عاقل دوبار از یه سوراخ گزیده نمی‌شه.",
    "کوه به کوه نمی‌رسه، آدم به آدم می‌رسه.",
    "هر که خربزه می‌خوره، پای لرزش هم می‌شینه.",
    "آب که سر از سر گذشت، چه یک وجب چه صد وجب.",
]

JOKES_FALLBACK = [
    "یارو رفته دکتر می‌گه دکتر یادم میره... دکتر می‌گه از کِی؟ می‌گه چی از کِی؟ 😄",
    "به کامپیوترم گفتم رمزتو بگو، گفت: 404 not found! 🤖",
    "رفتم آرایشگاه گفتم مثل بازیگرا کوتاه کن، الان مثل صحنه فیلم ترسناکم! ✂️",
    "دیشب خواب دیدم پولدار شدم، صبح بیدار شدم دیدم فقط خوابم زیاد شده! 😂",
    "به دوستم گفتم وای‌فای نداره خونه‌شون، گفت مگه هوا مهمه؟! 📶",
    "رفتم بانک گفتم حسابمو چک کن، گفت واقعاً می‌خوای؟ گفتم آره، گفت خب گریه نکن! 😅",
    "معلم پرسید فرق «شاید» و «حتماً» چیه؟ بچه گفت: شاید بیام مدرسه، حتماً نمیام! 🎒",
    "زنگ زدم پیتزا سفارش بدم، گفتن آدرس بدید، گفتم دلم! 🍕",
]

# پاسخ‌های کلاسیک «توپ جادویی هشت» - قابلیت جدید و سرگرم‌کننده
EIGHTBALL_ANSWERS = [
    "بله، قطعاً! ✅", "به احتمال زیاد آره 🙂", "نشونه‌ها می‌گن بله 🔮",
    "الان نمی‌تونم بگم، بعداً بپرس 🤔", "بهتره الان جوابشو نگم 🙊",
    "تمرکز کن و دوباره بپرس 🌀", "نه، اصلاً 🚫", "به احتمال زیاد نه ❌",
    "امیدت رو زیاد نکن 😅", "مطمئناً 💯",
]

# ------------------------------------------------------------
# 🎡 چرخ شانس - قابلیت جدید: یه چرخ شوخی که جایزه/اتفاق تصادفی بهت می‌ده
# ------------------------------------------------------------
WHEEL_PRIZES = [
    "🎉 تبریک! امروز افتخاری «خوش‌شانس‌ترین عضو گروه» رو گرفتی!",
    "☕ یه فنجون چای مجازی از طرف ربات بهت تعارف می‌شه.",
    "😴 امروز روز تنبلیته، به خودت سخت نگیر.",
    "📵 یه ساعت بدون گوشی امتحان کن، حالش رو ببر.",
    "🍕 امشب شب سفارش پیتزاست، دلت بخواد یا نخواد!",
    "🧹 نوبت توئه که گروه رو جارو بزنی (شوخی بود 😄).",
    "🎁 هیچی نبردی، ولی حداقل خندیدی!",
    "🚀 امروز روز شروع یه کار بزرگه، برو که رفتیم!",
    "🐌 امروز باید صبور باشی، کارها کمی کند پیش می‌رن.",
    "🏆 تو قهرمان بی‌رقیب امروز گروه هستی!",
]


def spin_wheel() -> str:
    return random.choice(WHEEL_PRIZES)


# ------------------------------------------------------------
# 🕵️ جرأت یا حقیقت - قابلیت جدید: بازی گروهی محبوب با دو دکمه
# ------------------------------------------------------------
TRUTH_QUESTIONS = [
    "بدترین کاری که تا حالا کردی و کسی نمی‌دونه چیه؟",
    "یه دروغ که زیاد می‌گی چیه؟",
    "اگه یه روز نامرئی می‌شدی چیکار می‌کردی؟",
    "خجالت‌آورترین خاطره‌ی مدرسه‌ت چی بود؟",
    "آخرین باری که گریه کردی کِی بود و چرا؟",
    "یه رازی که تا حالا به هیچ‌کس نگفتی؟",
    "بدترین سوتی‌ای که تا حالا دادی چی بود؟",
    "اگه یه ابرقدرت داشتی، اولین کارت باهاش چی بود؟",
]
DARE_ACTIONS = [
    "یه عکس از صفحه‌ی گالریت رو (هرچی بازش کردی) توی گروه بفرست!",
    "با صدای یه کارتون معروف یه جمله بگو (ویس بفرست).",
    "پروفایلت رو تا فردا بذار یه عکس خنده‌دار.",
    "به یه نفر توی گروه بگو چرا فکر می‌کنی خفنه (بدون شوخی!).",
    "یه شعر همین الان درباره‌ی گروه بساز و بفرست.",
    "۳۰ ثانیه فقط با ایموجی حرف بزن.",
    "اسم استیکر پروفایلت رو بذار «قهرمان امروز».",
    "یه دیالوگ از فیلم مورد علاقه‌ت رو بازی کن (متنی بنویس).",
]


def fetch_hafez_from_ganjoor():
    try:
        r = _http_session.get(
            "https://api.ganjoor.net/api/ganjoor/poem/random",
            params={"poetId": 2},
            timeout=8,
        )
        if r.status_code == 200:
            data = r.json()
            title = data.get("title", "")
            verses = data.get("verses", [])
            if verses:
                lines = [v.get("text", "") for v in verses[:4] if v.get("text")]
                if lines:
                    text = "\n".join(lines)
                    return f"{text}\n\n📌 از غزلیات حافظ - «{title}»"
    except Exception as e:
        logger.warning(f"Ganjoor fetch failed: {e}")
    return None


async def generate_hafez() -> str:
    # منبع واقعی و آنلاین: گنجور (api.ganjoor.net) - بزرگ‌ترین آرشیو شعر کلاسیک فارسی
    verse = await asyncio.to_thread(fetch_hafez_from_ganjoor)
    source_note = " (🌐 منبع: ganjoor.net)"
    if not verse:
        # اگه سایت در دسترس نبود، کاملاً آفلاین از دیوان حافظِ داخلیِ ربات میاد
        verse = random.choice(HAFEZ_VERSES)
        source_note = " (📴 آفلاین - از دیوان حافظ)"
    return f"📖 {verse}{source_note}"


async def generate_tarot() -> str:
    # ابتدا تلاش می‌کنه یه کارت واقعی از سایت tarotapi.dev (منبع آنلاینِ واقعی
    # و رایگان RWS Tarot) بگیره؛ اگه نشد یا نتونست match کنه، کاملاً آفلاین از
    # دکِ ۷۸ کارتیِ داخلی ربات یه کارت انتخاب می‌کنه - همیشه جواب می‌ده.
    online = await asyncio.to_thread(_fetch_tarot_card_online_blocking)
    online_note = ""
    mapped = None
    if online:
        mapped = map_tarotapi_card_to_persian(online.get("name_en", ""))

    reversed_card = random.random() < 0.3  # حدود ۳۰٪ موارد به‌صورت معکوس

    if mapped:
        card, base_meaning = mapped
        en_meaning = (online.get("meaning_rev") if reversed_card else online.get("meaning_up")) or ""
        if en_meaning:
            online_note = f"\n\n🌐 برداشت منبع بین‌المللی (tarotapi.dev):\n{en_meaning}"
    else:
        card, base_meaning = random.choice(TAROT_DECK_FULL)

    text = f"🃏 کارت: {card}{' (معکوس)' if reversed_card else ''}\n\n{base_meaning}"
    if reversed_card:
        text += TAROT_REVERSED_NOTE
    text += online_note
    text += f"\n\n{random.choice(TAROT_ADVICE_CLOSERS)}"
    return text



# ============================================================
# قیمت دلار و بیت‌کوین
# ============================================================
def fetch_usd_price():
    try:
        r = _http_session.get(
            "https://api.nobitex.ir/market/stats",
            params={"srcCurrency": "usdt", "dstCurrency": "rls"},
            timeout=7,
        )
        if r.status_code == 200:
            data = r.json()
            stats = data.get("stats", {}).get("usdt-rls", {})
            latest = stats.get("latest")
            if latest:
                toman = int(float(latest)) // 10
                if toman > 1000:
                    return toman, "نوبیتکس (نرخ تتر)"
    except Exception as e:
        logger.warning(f"Nobitex USD fetch failed: {e}")

    try:
        r = _http_session.get("https://call1.tgju.org/ajax.json", timeout=7)
        if r.status_code == 200:
            data = r.json()
            price_raw = data.get("current", {}).get("price_dollar_rl", {}).get("p")
            if price_raw:
                clean = str(price_raw).replace(",", "").strip()
                rial = int(clean)
                toman = rial // 10
                if toman > 1000:
                    return toman, "TGJU"
    except Exception as e:
        logger.warning(f"TGJU USD fetch failed: {e}")

    return None, None


def fetch_btc_price():
    try:
        r = _http_session.get(
            "https://api.coingecko.com/api/v3/simple/price",
            params={"ids": "bitcoin", "vs_currencies": "usd"},
            timeout=7,
        )
        if r.status_code == 200:
            return r.json()["bitcoin"]["usd"], "CoinGecko"
    except Exception as e:
        logger.warning(f"CoinGecko BTC fetch failed: {e}")

    try:
        r = _http_session.get(
            "https://api.nobitex.ir/market/stats",
            params={"srcCurrency": "btc", "dstCurrency": "usdt"},
            timeout=7,
        )
        if r.status_code == 200:
            data = r.json()
            stats = data.get("stats", {}).get("btc-usdt", {})
            latest = stats.get("latest")
            if latest:
                return float(latest), "نوبیتکس"
    except Exception as e:
        logger.warning(f"Nobitex BTC fetch failed: {e}")

    try:
        r = _http_session.get("https://api.coincap.io/v2/assets/bitcoin", timeout=7)
        if r.status_code == 200:
            price = float(r.json()["data"]["priceUsd"])
            return price, "CoinCap"
    except Exception as e:
        logger.warning(f"CoinCap BTC fetch failed: {e}")

    return None, None


async def fetch_prices():
    now = datetime.now()
    if PRICE_CACHE["data"] and PRICE_CACHE["time"] and now - PRICE_CACHE["time"] < timedelta(seconds=CACHE_SECONDS):
        return PRICE_CACHE["data"]

    (usd_toman, usd_source), (btc_usd, btc_source) = await asyncio.gather(
        asyncio.to_thread(fetch_usd_price),
        asyncio.to_thread(fetch_btc_price),
    )

    result = {
        "usd_toman": usd_toman, "usd_source": usd_source,
        "btc_usd": btc_usd, "btc_source": btc_source,
        "btc_toman": int(btc_usd * usd_toman) if (btc_usd and usd_toman) else None,
    }
    PRICE_CACHE["data"] = result
    PRICE_CACHE["time"] = now
    return result


# ============================================================
# منوی شیک (Inline Keyboard)
# ============================================================
def main_menu_keyboard():
    keyboard = [
        [InlineKeyboardButton("🔮 فال روزانه", callback_data="fal"),
         InlineKeyboardButton("🃏 تاروت", callback_data="tarot")],
        [InlineKeyboardButton("📖 فال حافظ", callback_data="hafez"),
         InlineKeyboardButton("🎯 شانس امروز", callback_data="shans")],
        [InlineKeyboardButton("💵 قیمت دلار", callback_data="dollar"),
         InlineKeyboardButton("₿ قیمت بیت‌کوین", callback_data="bitcoin")],
        [InlineKeyboardButton("😂 جوک", callback_data="joke"),
         InlineKeyboardButton("💬 ضرب‌المثل", callback_data="quote")],
        [InlineKeyboardButton("🎱 توپ جادویی", callback_data="eightball"),
         InlineKeyboardButton("🎡 چرخ شانس", callback_data="wheel")],
        [InlineKeyboardButton("🕵️ جرأت یا حقیقت", callback_data="td_start"),
         InlineKeyboardButton("🐺 بازی گرگینه", callback_data="start_werewolf")],
        [InlineKeyboardButton("🛡️ پنل مدیریت گروه", callback_data="adminpanel")],
        [InlineKeyboardButton("📜 قوانین گروه", callback_data="rules"),
         InlineKeyboardButton("ℹ️ راهنما", callback_data="help")],
    ]
    return InlineKeyboardMarkup(keyboard)


def admin_panel_keyboard(chat_id):
    reminder_on = bool(reminder_enabled.get(str(chat_id), False))
    reminder_label = "⏰ یادآور: 🟢 روشنه (خاموش کن)" if reminder_on else "⏰ یادآور: 🔴 خاموشه (روشن کن)"
    keyboard = [
        [InlineKeyboardButton("➕ افزودن الفاظ نامناسب", callback_data="badword_add_prompt")],
        [InlineKeyboardButton("📋 تعداد الفاظ فیلترشده", callback_data="badword_list")],
        [InlineKeyboardButton(reminder_label, callback_data="toggle_reminder")],
        [InlineKeyboardButton("⬅️ برگشت به منو", callback_data="back_main")],
    ]
    return InlineKeyboardMarkup(keyboard)


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    text = (
        "🤖 به دستیار هوشمند خوش اومدی! ✨\n\n"
        "من فقط یه ربات فال نیستم — دستیار کامل این گروهم: فال و تاروت با منبع واقعی آنلاین، "
        "بازی گروهی، مدیریت و نظم‌دهی، یادآور خودکار و کلی امکانات دیگه.\n"
        "از دکمه‌های زیر استفاده کن یا از منوی دستورات (کنار جعبه پیام).\n"
        "این ربات همچنین به‌صورت خودکار پیام‌های نامناسب رو تشخیص می‌ده."
    )
    await update.message.reply_text(text, reply_markup=main_menu_keyboard())


async def button_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    try:
        await query.answer()
    except Exception:
        pass

    data = query.data
    chat = query.message.chat

    if data.startswith("rps_"):
        await handle_rps_choice(query, data)
        return

    if data.startswith("ww_"):
        # این‌ها توسط ww_button_handler جدا مدیریت می‌شن؛ اینجا کاری نکن تا تداخل نشه.
        return

    if data == "td_truth":
        await query.message.reply_text(f"🕵️ حقیقت:\n\n{random.choice(TRUTH_QUESTIONS)}")
        return
    if data == "td_dare":
        await query.message.reply_text(f"🕵️ جرأت:\n\n{random.choice(DARE_ACTIONS)}")
        return
    if data == "td_start":
        kb = [[
            InlineKeyboardButton("🗣️ حقیقت", callback_data="td_truth"),
            InlineKeyboardButton("🔥 جرأت", callback_data="td_dare"),
        ]]
        await query.message.reply_text("🕵️ جرأت یا حقیقت؟ یکی رو انتخاب کن:", reply_markup=InlineKeyboardMarkup(kb))
        return

    if data == "start_werewolf":
        if chat.type == "private":
            await query.message.reply_text("🐺 این بازی فقط توی گروه قابل اجراست.")
        else:
            await ww_start_lobby(chat.id, query.from_user.id, context)
        return

    # -------------------- پنل مدیریت گروه --------------------
    if data == "adminpanel":
        if chat.type == "private":
            await query.message.reply_text("🛡️ پنل مدیریت فقط توی گروه معنی داره.")
            return
        if not await is_admin(update, context):
            await query.message.reply_text("⛔ این پنل فقط برای ادمین‌های گروهه.")
            return
        await query.message.reply_text(
            "🛡️ پنل مدیریت گروه:\n\nاز اینجا می‌تونی الفاظ نامناسب رو مدیریت کنی یا یادآور خودکار رو روشن/خاموش کنی.",
            reply_markup=admin_panel_keyboard(chat.id),
        )
        return

    if data == "back_main":
        await query.message.reply_text("منوی اصلی:", reply_markup=main_menu_keyboard())
        return

    if data == "badword_add_prompt":
        if chat.type == "private":
            await query.message.reply_text("⛔ این گزینه فقط توی گروه کار می‌کنه.")
            return
        if not await is_admin(update, context):
            await query.message.reply_text("⛔ فقط ادمین‌های گروه می‌تونن کلمه اضافه کنن.")
            return
        pending_badword_add[query.from_user.id] = chat.id
        await query.message.reply_text(
            "✏️ خب، حالا همون کلمه‌ی نامناسبی که می‌خوای فیلتر بشه رو توی همین گروه بفرست.\n"
            "(این پیام فقط از خودِ تو در همین گروه، به‌عنوان کلمه‌ی جدید ثبت می‌شه)"
        )
        return

    if data == "badword_list":
        if not await is_admin(update, context):
            await query.message.reply_text("⛔ فقط ادمین‌های گروه می‌تونن ببینن.")
            return
        default_count = len(BAD_WORDS_FA) + len(BAD_WORDS_EN)
        custom_count = len(get_custom_words_for_chat(chat.id))
        await query.message.reply_text(
            f"📋 کلمات فیلترشده‌ی پیش‌فرض: {default_count}\n"
            f"📋 کلمات سفارشیِ همین گروه: {custom_count}",
            reply_markup=admin_panel_keyboard(chat.id),
        )
        return

    if data == "toggle_reminder":
        if chat.type == "private":
            await query.message.reply_text("⛔ این گزینه فقط توی گروه کار می‌کنه.")
            return
        if not await is_admin(update, context):
            await query.message.reply_text("⛔ فقط ادمین‌های گروه می‌تونن این کارو بکنن.")
            return
        key = str(chat.id)
        current = bool(reminder_enabled.get(key, False))
        reminder_enabled[key] = not current
        async with _file_write_lock:
            save_json_safe(REMINDER_FILE, reminder_enabled)
        status_text = "🟢 روشن شد! از این به بعد ساعت‌های زوج و نیم (مثلاً ۸:۳۰) پیام «پاچیدن چاه» و سرِ ساعت‌های فرد (مثلاً ۹:۰۰) پیام «شام ننه‌جون» فرستاده می‌شه." \
            if not current else "🔴 خاموش شد."
        await query.message.reply_text(f"⏰ یادآور خودکار: {status_text}", reply_markup=admin_panel_keyboard(chat.id))
        return

    user_name = query.from_user.first_name or "دوست عزیز"

    try:
        if data == "fal":
            text = f"🔮 فال امروز {user_name}:\n\n{await generate_fal(user_name)}"
        elif data == "tarot":
            text = await generate_tarot()
        elif data == "hafez":
            text = await generate_hafez()
        elif data == "shans":
            text = f"🎯 شانس امروزت: {random.randint(1, 100)}٪"
        elif data == "eightball":
            text = f"🎱 {random.choice(EIGHTBALL_ANSWERS)}"
        elif data == "wheel":
            text = f"🎡 نتیجه‌ی چرخش:\n\n{spin_wheel()}"
        elif data == "dollar":
            p = await fetch_prices()
            text = (f"💵 قیمت دلار: {p['usd_toman']:,} تومان\n(منبع: {p['usd_source']})"
                    if p["usd_toman"] else "⚠️ فعلاً هیچ‌کدوم از منابع قیمت در دسترس نیستن، چند لحظه دیگه دوباره امتحان کن.")
        elif data == "bitcoin":
            p = await fetch_prices()
            if p["btc_usd"]:
                text = f"₿ قیمت بیت‌کوین: ${p['btc_usd']:,}\n(منبع: {p['btc_source']})"
                if p["btc_toman"]:
                    text += f"\nمعادل: {p['btc_toman']:,} تومان"
            else:
                text = "⚠️ فعلاً هیچ‌کدوم از منابع قیمت در دسترس نیستن، چند لحظه دیگه دوباره امتحان کن."
        elif data == "joke":
            text = f"😂 {random.choice(JOKES_FALLBACK)}"
        elif data == "quote":
            text = f"💬 {random.choice(PROVERBS_FA)}"
        elif data == "rules":
            text = (
                "📜 قوانین گروه:\n\n"
                "۱. احترام به همه اعضا الزامیه\n"
                "۲. استفاده از الفاظ رکیک ممنوعه (تشخیص خودکار)\n"
                "۳. تبلیغات بدون هماهنگی ادمین ممنوعه\n"
                "۴. اسپم و ارسال پی‌درپی پیام ممنوعه"
            )
        elif data == "help":
            text = (
                "ℹ️ راهنمای دستورات:\n\n"
                "🎉 سرگرمی: /fal /tarot /hafez /shans /eightball /wheel /td /joke /quote /compliment /roast /rps /coin /dice /love\n"
                "🐺 بازی گروهی: /gorgineh (شروع لابی گرگینه) /startgame /endgame /players\n"
                "💰 قیمت: /dollar /bitcoin /price\n"
                "👥 گروه: /rules /report /id /stats /botstatus\n"
                "🛡️ ادمین: /mute /unmute /kick /ban /warn /pin /unpin /purge /addbad /removebad /listbad\n"
                "🛡️ پنل مدیریت شیشه‌ای (افزودن الفاظ + یادآور خودکار): دکمه «پنل مدیریت گروه» توی /start"
            )
        else:
            text = "دستور نامشخص."
    except Exception as e:
        logger.error(f"خطا در button_handler: {e}")
        text = "⚠️ یه مشکل موقتی پیش اومد، لطفاً دوباره امتحان کن."

    try:
        await query.message.reply_text(text, reply_markup=main_menu_keyboard())
    except BadRequest as e:
        logger.warning(f"خطای ارسال پیام دکمه: {e}")
        await query.message.reply_text(text[:4000])


# ============================================================
# دستورات فال
# ============================================================
async def fal_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    name = update.effective_user.first_name or "دوست عزیز"
    await update.message.reply_text(f"🔮 فال امروز {name}:\n\n{await generate_fal(name)}")


async def tarot_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(await generate_tarot())


async def hafez_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(await generate_hafez())


async def shans_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(f"🎯 شانس امروزت: {random.randint(1, 100)}٪")


async def eightball_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(f"🎱 {random.choice(EIGHTBALL_ANSWERS)}")


async def wheel_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(f"🎡 نتیجه‌ی چرخش:\n\n{spin_wheel()}")


async def td_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    kb = [[
        InlineKeyboardButton("🗣️ حقیقت", callback_data="td_truth"),
        InlineKeyboardButton("🔥 جرأت", callback_data="td_dare"),
    ]]
    await update.message.reply_text("🕵️ جرأت یا حقیقت؟ یکی رو انتخاب کن:", reply_markup=InlineKeyboardMarkup(kb))


async def rules_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    text = (
        "📜 قوانین گروه:\n\n"
        "۱. احترام به همه اعضا الزامیه\n"
        "۲. استفاده از الفاظ رکیک ممنوعه (تشخیص خودکار)\n"
        "۳. تبلیغات بدون هماهنگی ادمین ممنوعه\n"
        "۴. اسپم و ارسال پی‌درپی پیام ممنوعه"
    )
    await update.message.reply_text(text)


async def dollar_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    p = await fetch_prices()
    text = (f"💵 قیمت دلار: {p['usd_toman']:,} تومان\n(منبع: {p['usd_source']})"
            if p["usd_toman"] else "⚠️ فعلاً هیچ‌کدوم از منابع قیمت در دسترس نیستن.")
    await update.message.reply_text(text)


async def bitcoin_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    p = await fetch_prices()
    if p["btc_usd"]:
        text = f"₿ قیمت بیت‌کوین: ${p['btc_usd']:,}\n(منبع: {p['btc_source']})"
        if p["btc_toman"]:
            text += f"\nمعادل: {p['btc_toman']:,} تومان"
    else:
        text = "⚠️ فعلاً هیچ‌کدوم از منابع قیمت در دسترس نیستن."
    await update.message.reply_text(text)


async def price_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    p = await fetch_prices()
    lines = ["📊 قیمت‌های لحظه‌ای:\n"]
    lines.append(f"💵 دلار: {p['usd_toman']:,} تومان ({p['usd_source']})" if p["usd_toman"] else "💵 دلار: نامشخص")
    lines.append(f"₿ بیت‌کوین: ${p['btc_usd']:,} ({p['btc_source']})" if p["btc_usd"] else "₿ بیت‌کوین: نامشخص")
    await update.message.reply_text("\n".join(lines))


async def id_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    chat = update.effective_chat
    text = f"👤 آیدی تو: {user.id}\n💬 آیدی این چت: {chat.id}"
    if update.message.reply_to_message:
        target = update.message.reply_to_message.from_user
        text += f"\n🎯 آیدی کاربر ریپلای‌شده: {target.id}"
    await update.message.reply_text(text)


# ============================================================
# پنل مدیریت گروه (دستور متنی جایگزین دکمه، برای راحتی)
# ============================================================
async def adminpanel_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat = update.effective_chat
    if chat.type == "private":
        await update.message.reply_text("🛡️ این پنل فقط توی گروه معنی داره.")
        return
    if not await is_admin(update, context):
        await update.message.reply_text("⛔ این پنل فقط برای ادمین‌های گروهه.")
        return
    await update.message.reply_text(
        "🛡️ پنل مدیریت گروه:\n\nاز اینجا می‌تونی الفاظ نامناسب رو مدیریت کنی یا یادآور خودکار رو روشن/خاموش کنی.",
        reply_markup=admin_panel_keyboard(chat.id),
    )


# ============================================================
# دستورات سرگرمی
# ============================================================
def get_target_user(update: Update):
    if update.message.reply_to_message:
        return update.message.reply_to_message.from_user
    return None


async def joke_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(f"😂 {random.choice(JOKES_FALLBACK)}")


async def quote_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(f"💬 {random.choice(PROVERBS_FA)}")


COMPLIMENTS_FA = [
    "{name} جان، همینکه هستی کافیه که روز آدم رو بسازه! ✨",
    "{name}، حضورت مثل یه خبر خوب می‌مونه! 🌟",
    "بگم {name} خفنه کم گفتم، افسانه‌ست! 🔥",
    "{name} جان، لبخندت دلیل خوب بودن امروزه! 😄",
    "هر جا {name} باشه، شادی هم هست! 🎉",
    "{name}، تو دقیقاً همونی که همه آرزوشو دارن! 💎",
]
ROASTS_FA = [
    "{name} جان، امروز حسابی سوژه شدی! 😄",
    "{name}، انگار امروز نوبت توئه که بخندونی‌مون! 😂",
    "{name} جان، یکی بگه امروز آروم‌تر باش! 😆",
    "{name}، همیشه یه چیزی برای خندوندن داری! 🤭",
    "{name} جان، امروز افتخاری «سوژه‌ی گروه» رو گرفتی! 🏅",
]


async def compliment_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    target = get_target_user(update)
    name = target.first_name if target else update.effective_user.first_name
    await update.message.reply_text(random.choice(COMPLIMENTS_FA).format(name=name))


async def roast_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    target = get_target_user(update)
    if not target:
        await update.message.reply_text("روی پیام کسی که می‌خوای بهش متلک بامزه بندازی ریپلای بزن و بنویس /roast")
        return
    name = target.first_name
    await update.message.reply_text(random.choice(ROASTS_FA).format(name=name))


async def love_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    target = get_target_user(update)
    name1 = user.first_name
    name2 = target.first_name if target else (" ".join(context.args) if context.args else None)
    if not name2:
        await update.message.reply_text("یا روی پیام کسی ریپلای بزن، یا بنویس: /love اسم")
        return
    percent = sum(ord(c) for c in (name1 + name2)) % 101
    bar = "❤️" * (percent // 10) + "🖤" * (10 - percent // 10)
    await update.message.reply_text(f"💘 عشق‌سنج {name1} و {name2}:\n{bar}\n{percent}٪")


async def coin_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(f"🪙 نتیجه: {random.choice(['شیر', 'خط'])}")


async def dice_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(f"🎲 عدد تاس: {random.randint(1, 6)}")


RPS_EMOJI = {"rock": "🪨", "paper": "📄", "scissors": "✂️"}
RPS_FA = {"rock": "سنگ", "paper": "کاغذ", "scissors": "قیچی"}


def rps_outcome(user_choice, bot_choice):
    if user_choice == bot_choice:
        return "مساوی"
    beats = {"rock": "scissors", "paper": "rock", "scissors": "paper"}
    return "برد" if beats[user_choice] == bot_choice else "باخت"


async def rps_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    keyboard = [[
        InlineKeyboardButton("🪨 سنگ", callback_data="rps_rock"),
        InlineKeyboardButton("📄 کاغذ", callback_data="rps_paper"),
        InlineKeyboardButton("✂️ قیچی", callback_data="rps_scissors"),
    ]]
    await update.message.reply_text("یکی رو انتخاب کن:", reply_markup=InlineKeyboardMarkup(keyboard))


async def handle_rps_choice(query, data):
    user_choice = data.split("_", 1)[1]
    bot_choice = random.choice(list(RPS_EMOJI.keys()))
    outcome = rps_outcome(user_choice, bot_choice)
    outcome_fa = {"برد": "بردی! 🎉", "باخت": "باختی! 😅", "مساوی": "مساوی شدیم! 🤝"}[outcome]
    text = (
        f"تو: {RPS_EMOJI[user_choice]} {RPS_FA[user_choice]}\n"
        f"من: {RPS_EMOJI[bot_choice]} {RPS_FA[bot_choice]}\n\n{outcome_fa}"
    )
    await query.message.reply_text(text)


# ============================================================
# مدیریت لیست کلمات نامناسب (دستورات متنی قدیمی - همچنان کار می‌کنن)
# ============================================================
async def addbad_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        await update.message.reply_text("⛔ فقط ادمین‌های گروه می‌تونن کلمه اضافه کنن.")
        return
    if not context.args:
        await update.message.reply_text("استفاده: /addbad کلمه_موردنظر")
        return
    word = " ".join(context.args).strip().lower()
    await add_custom_bad_word(update.effective_chat.id, word)
    await update.message.reply_text(f"✅ کلمه «{word}» به لیست سفارشی این گروه اضافه شد.")


async def add_custom_bad_word(chat_id, word: str):
    """کلمه رو توی فضای ذخیره‌سازی جداگانه‌ی سرور (bad_words_custom.json) برای همون گروه ثبت می‌کنه."""
    key = str(chat_id)
    async with _file_write_lock:
        words = custom_bad_words.setdefault(key, [])
        if word not in words:
            words.append(word)
            save_json_safe(CUSTOM_BAD_WORDS_FILE, custom_bad_words)


async def removebad_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        await update.message.reply_text("⛔ فقط ادمین‌های گروه می‌تونن کلمه حذف کنن.")
        return
    if not context.args:
        await update.message.reply_text("استفاده: /removebad کلمه_موردنظر")
        return
    word = " ".join(context.args).strip().lower()
    removed = False
    if word in BAD_WORDS_FA:
        BAD_WORDS_FA.remove(word)
        removed = True
    if word in BAD_WORDS_EN:
        BAD_WORDS_EN.remove(word)
        removed = True
    key = str(update.effective_chat.id)
    if word in custom_bad_words.get(key, []):
        custom_bad_words[key].remove(word)
        async with _file_write_lock:
            save_json_safe(CUSTOM_BAD_WORDS_FILE, custom_bad_words)
        removed = True
    if removed:
        save_json_safe(BAD_WORDS_FILE, {"fa": BAD_WORDS_FA, "en": BAD_WORDS_EN})
        await update.message.reply_text(f"✅ کلمه «{word}» از لیست حذف شد.")
    else:
        await update.message.reply_text("این کلمه توی لیست نبود.")


async def listbad_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        await update.message.reply_text("⛔ فقط ادمین‌های گروه می‌تونن ببینن.")
        return
    default_count = len(BAD_WORDS_FA) + len(BAD_WORDS_EN)
    custom_count = len(get_custom_words_for_chat(update.effective_chat.id))
    await update.message.reply_text(
        f"📋 کلمات فیلترشده‌ی پیش‌فرض: {default_count}\n📋 کلمات سفارشیِ همین گروه: {custom_count}"
    )


# ============================================================
# دستورات مدیریتی گروه (فقط ادمین)
# ============================================================
async def mute_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        await update.message.reply_text("⛔ فقط ادمین‌ها می‌تونن این کار رو بکنن.")
        return
    target = get_target_user(update)
    if not target:
        await update.message.reply_text("روی پیام فردی که می‌خوای سکوتش کنی ریپلای بزن و بنویس /mute")
        return
    try:
        await context.bot.restrict_chat_member(
            update.effective_chat.id, target.id,
            permissions=ChatPermissions(can_send_messages=False),
        )
        await update.message.reply_text(f"🔇 {target.first_name} تا اطلاع بعدی سکوت شد.")
    except TelegramError as e:
        await update.message.reply_text(f"⚠️ نشد: {e}\n\nاحتمالاً من توی این گروه ادمین نیستم یا دسترسی محدودسازی اعضا رو ندارم. با /botstatus وضعیتم رو چک کن.")


async def unmute_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        await update.message.reply_text("⛔ فقط ادمین‌ها می‌تونن این کار رو بکنن.")
        return
    target = get_target_user(update)
    if not target:
        await update.message.reply_text("روی پیام فردی که می‌خوای صداش رو باز کنی ریپلای بزن و بنویس /unmute")
        return
    try:
        await context.bot.restrict_chat_member(
            update.effective_chat.id, target.id,
            permissions=ChatPermissions(
                can_send_messages=True, can_send_audios=True, can_send_photos=True,
                can_send_videos=True, can_send_other_messages=True,
            ),
        )
        await update.message.reply_text(f"🔊 {target.first_name} دوباره می‌تونه پیام بده.")
    except TelegramError as e:
        await update.message.reply_text(f"⚠️ نشد: {e}")


async def kick_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        await update.message.reply_text("⛔ فقط ادمین‌ها می‌تونن این کار رو بکنن.")
        return
    target = get_target_user(update)
    if not target:
        await update.message.reply_text("روی پیام فردی که می‌خوای اخراجش کنی ریپلای بزن و بنویس /kick")
        return
    try:
        chat_id = update.effective_chat.id
        await context.bot.ban_chat_member(chat_id, target.id)
        await context.bot.unban_chat_member(chat_id, target.id)
        await update.message.reply_text(f"👢 {target.first_name} از گروه اخراج شد.")
    except TelegramError as e:
        await update.message.reply_text(f"⚠️ نشد: {e}")


async def ban_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        await update.message.reply_text("⛔ فقط ادمین‌ها می‌تونن این کار رو بکنن.")
        return
    target = get_target_user(update)
    if not target:
        await update.message.reply_text("روی پیام فردی که می‌خوای بنش کنی ریپلای بزن و بنویس /ban")
        return
    try:
        await context.bot.ban_chat_member(update.effective_chat.id, target.id)
        await update.message.reply_text(f"⛔ {target.first_name} برای همیشه بن شد.")
    except TelegramError as e:
        await update.message.reply_text(f"⚠️ نشد: {e}")


async def warn_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        await update.message.reply_text("⛔ فقط ادمین‌ها می‌تونن این کار رو بکنن.")
        return
    target = get_target_user(update)
    if not target:
        await update.message.reply_text("روی پیام فردی که می‌خوای اخطار بدی ریپلای بزن و بنویس /warn")
        return
    await apply_warn(update, context, target, reason="دستور دستی ادمین")


async def apply_warn(update, context, target_user, reason: str):
    chat_id = update.effective_chat.id
    key = f"{chat_id}:{target_user.id}"
    warns_data[key] = warns_data.get(key, 0) + 1
    save_json_safe(WARN_FILE, warns_data)
    count = warns_data[key]

    if count >= 3:
        try:
            await context.bot.restrict_chat_member(
                chat_id, target_user.id, permissions=ChatPermissions(can_send_messages=False),
            )
            warns_data[key] = 0
            save_json_safe(WARN_FILE, warns_data)
            await update.effective_chat.send_message(
                f"🔇 {target_user.first_name} به دلیل ۳ اخطار ({reason}) به‌صورت خودکار سکوت شد.\n"
                f"ادمین‌ها می‌تونن با /unmute (ریپلای روی پیامش) بازش کنن."
            )
        except TelegramError as e:
            logger.warning(f"خطای سکوت خودکار: {e}")
    else:
        await update.effective_chat.send_message(
            f"⚠️ اخطار {count}/۳ برای {target_user.first_name} ({reason})."
        )


async def pin_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        await update.message.reply_text("⛔ فقط ادمین‌ها می‌تونن این کار رو بکنن.")
        return
    if not update.message.reply_to_message:
        await update.message.reply_text("روی پیامی که می‌خوای پین کنی ریپلای بزن و بنویس /pin")
        return
    try:
        await context.bot.pin_chat_message(update.effective_chat.id, update.message.reply_to_message.message_id)
        await update.message.reply_text("📌 پیام پین شد.")
    except TelegramError as e:
        await update.message.reply_text(f"⚠️ نشد: {e}")


async def unpin_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        await update.message.reply_text("⛔ فقط ادمین‌ها می‌تونن این کار رو بکنن.")
        return
    try:
        await context.bot.unpin_chat_message(update.effective_chat.id)
        await update.message.reply_text("📌 پین پیام برداشته شد.")
    except TelegramError as e:
        await update.message.reply_text(f"⚠️ نشد: {e}")


async def purge_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        await update.message.reply_text("⛔ فقط ادمین‌ها می‌تونن این کار رو بکنن.")
        return
    if not context.args or not context.args[0].isdigit():
        await update.message.reply_text("استفاده: /purge تعداد  (مثلاً /purge 10 — حداکثر ۱۰۰)")
        return
    n = min(int(context.args[0]), 100)
    chat_id = update.effective_chat.id
    start_id = update.message.message_id
    deleted = 0
    for mid in range(start_id, start_id - n - 1, -1):
        try:
            await context.bot.delete_message(chat_id, mid)
            deleted += 1
        except TelegramError:
            continue
    await context.bot.send_message(chat_id, f"🧹 {deleted} پیام پاک شد.")


async def botstatus_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat = update.effective_chat
    if chat.type == "private":
        await update.message.reply_text("این دستور فقط توی گروه معنی داره.")
        return
    try:
        member = await context.bot.get_chat_member(chat.id, context.bot.id)
        lines = [f"🤖 وضعیت من توی «{chat.title}»: {member.status}"]
        if member.status == "administrator":
            perms = {
                "حذف پیام": member.can_delete_messages,
                "محدود/سکوت کردن اعضا": member.can_restrict_members,
                "پین کردن پیام": member.can_pin_messages,
                "دعوت با لینک": member.can_invite_users,
            }
            for label, val in perms.items():
                lines.append(f"{'✅' if val else '❌'} {label}")
        else:
            lines.append(
                "\n⚠️ من الان ادمین این گروه نیستم، برای همین دستورات /mute /kick /ban /warn کار نمی‌کنن.\n\n"
                "برای ادمین کردنم (این کار رو فقط مالک یا یه ادمین دیگه‌ی گروه می‌تونه انجام بده، ربات نمی‌تونه خودشو ادمین کنه):\n"
                "۱. پروفایل گروه → Administrators → Add Admin\n"
                "۲. من رو از لیست اعضا انتخاب کن\n"
                "۳. حداقل «Delete messages» و «Ban/Restrict users» رو فعال کن\n"
                "۴. ذخیره کن"
            )
        await update.message.reply_text("\n".join(lines))
    except TelegramError as e:
        await update.message.reply_text(f"⚠️ نشد وضعیتم رو بگیرم: {e}")


# ============================================================
# فیلتر ناسزا + ضد اسپم + ترجمه شعر + حالت «افزودن کلمه» روی پیام‌های گروه
# ============================================================
async def handle_group_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message or not update.message.text:
        return
    text = update.message.text
    user = update.effective_user
    chat = update.effective_chat

    if user.is_bot:
        return

    # --- اولویت اول: آیا این ادمین الان توی «حالت افزودن کلمه نامناسب»ه؟ ---
    # این چک قبل از هر پردازش دیگه‌ای انجام می‌شه تا با فیلتر ناسزا یا ترجمه تداخل نکنه،
    # چون خودِ کلمه‌ی جدید ممکنه یه ناسزا باشه و نباید به‌عنوان پیام عادی پردازش بشه.
    pending_chat = pending_badword_add.get(user.id)
    if pending_chat is not None and pending_chat == chat.id:
        word = text.strip().lower()
        del pending_badword_add[user.id]
        if not word:
            await update.message.reply_text("⚠️ متن خالی بود، دوباره از پنل مدیریت امتحان کن.")
            return
        await add_custom_bad_word(chat.id, word)
        await update.message.reply_text(
            f"✅ کلمه «{word}» به لیست الفاظ نامناسب این گروه اضافه شد.\n"
            f"از این به بعد اگه کسی این کلمه رو بگه، بهش اخطار داده می‌شه."
        )
        return

    # --- ضد اسپم (flood control) ---
    now = time.time()
    times = user_message_times[f"{chat.id}:{user.id}"]
    times.append(now)
    if len(times) == FLOOD_LIMIT and (now - times[0]) < FLOOD_WINDOW:
        try:
            until = datetime.now() + timedelta(minutes=5)
            await context.bot.restrict_chat_member(
                chat.id, user.id,
                permissions=ChatPermissions(can_send_messages=False),
                until_date=until,
            )
            await update.message.reply_text(
                f"🚫 {user.first_name} به دلیل ارسال پیام زیاد و پشت‌سرهم، ۵ دقیقه سکوت شد."
            )
        except TelegramError as e:
            logger.warning(f"خطای ضد اسپم: {e}")
        return

    # --- فیلتر ناسزا (شامل کلمات پیش‌فرض + کلمات سفارشی همین گروه) ---
    if contains_bad_word(text, chat_id=chat.id):
        mention = mention_html(user)
        try:
            await update.message.reply_text(
                f"⚠️ {mention} لطفاً از الفاظ نامناسب استفاده نکن. این پیام گزارش شد.",
                parse_mode="HTML",
            )
        except Exception as e:
            logger.warning(f"خطای اخطار: {e}")

        try:
            admins = await context.bot.get_chat_administrators(chat.id)
            admin_mentions = [mention_html(a.user) for a in admins if not a.user.is_bot]
            if admin_mentions:
                await context.bot.send_message(
                    chat_id=chat.id,
                    text=f"🚨 توجه ادمین‌ها {' '.join(admin_mentions)}:\nکاربر {mention} از الفاظ نامناسب استفاده کرد.",
                    parse_mode="HTML",
                )
        except Exception as e:
            logger.warning(f"خطای اطلاع به ادمین: {e}")

        await apply_warn(update, context, user, reason="استفاده از الفاظ نامناسب")
        return

    # --- پاسخ‌گویی هوشمندِ ساده (قانون‌محور، کاملاً آفلاین) ---
    # فقط وقتی فعال می‌شه که پیام مستقیماً خطاب به رباته (کلمه‌ی «ربات» توش
    # باشه یا ریپلای روی پیام خودِ ربات باشه)، تا مزاحم گفت‌وگوی عادی گروه نشه.
    is_reply_to_bot = bool(
        update.message.reply_to_message
        and update.message.reply_to_message.from_user
        and update.message.reply_to_message.from_user.id == context.bot.id
    )
    if is_reply_to_bot or "ربات" in text:
        reply = smart_rule_based_reply(text, user.first_name or "دوست عزیز")
        if reply:
            await update.message.reply_text(reply)
        return


# ============================================================
# گزارش به ادمین‌ها (/report روی یه پیام)
# ============================================================
async def report_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not update.message.reply_to_message:
        await update.message.reply_text("روی پیامی که می‌خوای گزارش بدی ریپلای بزن و بنویس /report")
        return
    reporter = update.effective_user
    reported_msg = update.message.reply_to_message
    chat = update.effective_chat
    try:
        admins = await context.bot.get_chat_administrators(chat.id)
        admin_mentions = [mention_html(a.user) for a in admins if not a.user.is_bot]
        await context.bot.send_message(
            chat_id=chat.id,
            text=(
                f"🚨 گزارش جدید از طرف {mention_html(reporter)}:\n"
                f"پیام گزارش‌شده از: {mention_html(reported_msg.from_user)}\n\n"
                f"{' '.join(admin_mentions)}"
            ),
            parse_mode="HTML",
            reply_to_message_id=reported_msg.message_id,
        )
        await update.message.reply_text("✅ گزارش به ادمین‌ها ارسال شد.")
    except Exception as e:
        logger.warning(f"خطای گزارش: {e}")
        await update.message.reply_text("⚠️ گزارش ارسال نشد، دوباره امتحان کن.")


# ============================================================
# خوش‌آمدگویی و بدرقه اعضا
# ============================================================
async def welcome_new_member(update: Update, context: ContextTypes.DEFAULT_TYPE):
    for member in update.message.new_chat_members:
        if member.is_bot:
            continue
        text = (
            f"👋 سلام {member.first_name} عزیز، به گروه خوش اومدی!\n\n"
            f"لطفاً قوانین گروه رو با /rules ببین، و برای دیدن امکانات دستیار هوشمند /start رو بزن. خوش بگذره! 🎉"
        )
        await update.message.reply_text(text)


async def member_left(update: Update, context: ContextTypes.DEFAULT_TYPE):
    member = update.message.left_chat_member
    if member and not member.is_bot:
        await update.message.reply_text(f"👋 {member.first_name} از گروه رفت. به امید دیدار دوباره!")


# ============================================================
# آمار گروه
# ============================================================
async def stats_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat = update.effective_chat
    try:
        count = await context.bot.get_chat_member_count(chat.id)
        admins = await context.bot.get_chat_administrators(chat.id)
        custom_count = len(get_custom_words_for_chat(chat.id))
        text = (
            f"📊 آمار گروه «{chat.title}»:\n\n"
            f"👥 تعداد اعضا: {count}\n"
            f"👑 تعداد ادمین‌ها: {len(admins)}\n"
            f"📋 تعداد کلمات فیلترشده (پیش‌فرض): {len(BAD_WORDS_FA) + len(BAD_WORDS_EN)}\n"
            f"📋 تعداد کلمات سفارشیِ همین گروه: {custom_count}\n"
            f"⏰ یادآور خودکار: {'🟢 روشن' if reminder_enabled.get(str(chat.id), False) else '🔴 خاموش'}"
        )
    except Exception as e:
        text = f"⚠️ نشد آمار رو بگیرم: {e}"
    await update.message.reply_text(text)


# ============================================================
# ⏰ یادآور زمان‌بندی‌شده (JobQueue)
# این دو تا کاملاً باهم فرق دارن، هر کدوم فقط سرِ یه لحظه‌ی مشخص فعال می‌شن:
#   • «وقت پاچیدن چاهه» → فقط توی ساعت‌های زوج، دقیقه‌ی ۳۰ (مثلاً ۸:۳۰، ۱۰:۳۰، ۱۲:۳۰...)
#   • «شام ننه‌جون سرد شد» → فقط توی ساعت‌های فرد، دقیقه‌ی ۰۰ یعنی سرِ ساعت (مثلاً ۹:۰۰، ۱۱:۰۰...)
# هر ۶۰ ثانیه یه بار چک می‌کنه؛ برای هر گروه فقط یه بار در همون اسلات مشخص می‌فرسته
# (با کلید last-sent، ترکیب تاریخ+ساعت+دقیقه) تا تکراری نشه.
# ============================================================
async def reminder_check_job(context: ContextTypes.DEFAULT_TYPE):
    now = datetime.now()

    text = None
    if now.hour % 2 == 0 and now.minute == 30:
        text = REMINDER_EVEN_TEXT
    elif now.hour % 2 == 1 and now.minute == 0:
        text = REMINDER_ODD_TEXT
    else:
        return  # الان زمان هیچ‌کدوم از دو یادآور نیست

    current_slot = (now.date().isoformat(), now.hour, now.minute)
    for chat_id_str, enabled in list(reminder_enabled.items()):
        if not enabled:
            continue
        try:
            chat_id = int(chat_id_str)
        except ValueError:
            continue
        last_slot = reminder_last_sent_hour.get(chat_id_str)
        if last_slot == current_slot:
            continue  # همین لحظه‌ی مشخص قبلاً فرستاده شده
        reminder_last_sent_hour[chat_id_str] = current_slot
        try:
            await context.bot.send_message(chat_id, text)
        except TelegramError as e:
            logger.warning(f"خطای ارسال یادآور به {chat_id}: {e}")


# ============================================================
# بازی گروهی گرگینه (روستا در خطر)
# ============================================================
WW_MIN_PLAYERS = 3
WW_MAX_PLAYERS = 16
WW_JOIN_SECONDS = 45
WW_NIGHT_SECONDS = 40
WW_DAY_DISCUSSION_SECONDS = 45
WW_VOTE_SECONDS = 30

WW_ROLE_FA = {"wolf": "🐺 گرگ", "seer": "🔮 پیشگو", "doctor": "💉 دکتر", "villager": "👤 روستایی"}
WW_ROLE_DESC = {
    "wolf": "هر شب همراه بقیه‌ی گرگ‌ها یه نفر رو انتخاب می‌کنی که کشته بشه. اگه تعداد گرگ‌ها به روستایی‌ها برسه، گرگ‌ها می‌برن. 🐺",
    "seer": "هر شب می‌تونی یه نفر رو چک کنی و بفهمی گرگه یا نه. کمک کن روستایی‌ها گرگ‌ها رو پیدا کنن. 🔮",
    "doctor": "هر شب می‌تونی یه نفر (حتی خودت) رو از کشته‌شدن نجات بدی. 💉",
    "villager": "قدرت خاصی نداری، ولی رأیت روزها مهمه؛ سعی کن با بحث گرگ‌ها رو لو بدی. 👤",
}

ww_games = {}
ww_player_game = {}


class WWPlayer:
    def __init__(self, user):
        self.id = user.id
        self.name = user.first_name or "بازیکن"
        self.role = None
        self.alive = True


class WWGame:
    def __init__(self, chat_id, host_id):
        self.chat_id = chat_id
        self.host_id = host_id
        self.state = "lobby"
        self.players = {}
        self.round_no = 0
        self.night_kill_votes = {}
        self.seer_acted = False
        self.doctor_save = None
        self.last_victim_id = None
        self.last_saved = False
        self.day_votes = {}

    def alive_players(self):
        return [p for p in self.players.values() if p.alive]


def ww_assign_roles(player_ids):
    n = len(player_ids)
    wolves_count = max(1, n // 4)
    roles = ["wolf"] * wolves_count
    remaining = n - wolves_count
    if remaining >= 1 and n >= 5:
        roles.append("seer")
        remaining -= 1
    if remaining >= 1 and n >= 6:
        roles.append("doctor")
        remaining -= 1
    roles += ["villager"] * remaining
    random.shuffle(roles)
    return dict(zip(player_ids, roles))


def ww_check_win(game: "WWGame"):
    alive = game.alive_players()
    wolves = [p for p in alive if p.role == "wolf"]
    others = [p for p in alive if p.role != "wolf"]
    if len(wolves) == 0:
        return "village"
    if len(wolves) >= len(others):
        return "wolves"
    return None


def ww_cleanup_game(chat_id):
    game = ww_games.pop(chat_id, None)
    if game:
        for uid in list(game.players.keys()):
            if ww_player_game.get(uid) == chat_id:
                ww_player_game.pop(uid, None)


async def ww_start_lobby(chat_id, host_id, context: ContextTypes.DEFAULT_TYPE):
    if chat_id in ww_games and ww_games[chat_id].state != "ended":
        await context.bot.send_message(chat_id, "🐺 یه بازی از قبل توی این گروه در جریانه یا لابیش بازه.")
        return
    game = WWGame(chat_id, host_id)
    ww_games[chat_id] = game
    kb = [[InlineKeyboardButton("🐺 پیوستن به بازی", callback_data="ww_join")]]
    await context.bot.send_message(
        chat_id,
        (
            "🐺 بازی گرگینه (روستا در خطر) شروع شد!\n"
            f"حداقل {WW_MIN_PLAYERS} و حداکثر {WW_MAX_PLAYERS} نفر می‌تونن بازی کنن.\n"
            f"برای پیوستن دکمه‌ی زیر رو بزن، {WW_JOIN_SECONDS} ثانیه وقت داری.\n\n"
            "⚠️ حتماً قبلش یه‌بار توی خصوصی به من پیام بده (/start)، وگرنه نمی‌تونم نقشتو برات بفرستم.\n"
            "ادمین می‌تونه با /startgame زودتر شروع کنه یا با /endgame لغوش کنه."
        ),
        reply_markup=InlineKeyboardMarkup(kb),
    )
    context.application.create_task(ww_lobby_countdown(chat_id, context))


async def ww_lobby_countdown(chat_id, context: ContextTypes.DEFAULT_TYPE):
    await asyncio.sleep(WW_JOIN_SECONDS)
    game = ww_games.get(chat_id)
    if game and game.state == "lobby":
        await ww_try_start_game(chat_id, context)


async def ww_try_start_game(chat_id, context: ContextTypes.DEFAULT_TYPE):
    game = ww_games.get(chat_id)
    if not game or game.state != "lobby":
        return
    if len(game.players) < WW_MIN_PLAYERS:
        await context.bot.send_message(chat_id, f"❌ تعداد بازیکن‌ها کافی نبود (حداقل {WW_MIN_PLAYERS} نفر لازمه). بازی لغو شد.")
        ww_cleanup_game(chat_id)
        return

    roles = ww_assign_roles(list(game.players.keys()))
    for uid, role in roles.items():
        game.players[uid].role = role

    lines = ["🎭 نقش‌ها پخش شد! هر کس نقشش رو توی خصوصی می‌بینه.\n\n👥 بازیکنان:"]
    for p in game.players.values():
        lines.append(f"• {p.name}")
    await context.bot.send_message(chat_id, "\n".join(lines))

    for p in game.players.values():
        try:
            await context.bot.send_message(
                p.id, f"🎭 نقش تو توی این بازی: {WW_ROLE_FA[p.role]}\n\n{WW_ROLE_DESC[p.role]}"
            )
        except Forbidden:
            await context.bot.send_message(
                chat_id,
                f"⚠️ {p.name} عزیز، نتونستم نقشتو خصوصی بفرستم؛ اول به من پیام بده (/start) و دفعه بعد دوباره بازی کن.",
            )

    game.state = "night"
    context.application.create_task(ww_game_loop(chat_id, context))


async def ww_game_loop(chat_id, context: ContextTypes.DEFAULT_TYPE):
    game = ww_games[chat_id]
    try:
        while True:
            await ww_run_night(chat_id, context)
            winner = ww_check_win(game)
            if winner:
                await ww_announce_winner(chat_id, context, winner)
                break
            winner = await ww_run_day(chat_id, context)
            if winner:
                await ww_announce_winner(chat_id, context, winner)
                break
    except Exception as e:
        logger.error(f"خطا توی حلقه بازی گرگینه: {e}")
        await context.bot.send_message(chat_id, "⚠️ یه مشکل غیرمنتظره توی بازی پیش اومد و بازی متوقف شد.")
    finally:
        ww_cleanup_game(chat_id)


async def ww_run_night(chat_id, context: ContextTypes.DEFAULT_TYPE):
    game = ww_games[chat_id]
    game.state = "night"
    game.round_no += 1
    game.night_kill_votes = {}
    game.seer_acted = False
    game.doctor_save = None

    await context.bot.send_message(chat_id, f"🌙 شب {game.round_no} فرا رسید. همه بخوابید... نقش‌های خاص، به خصوصی من مراجعه کنید.")

    alive = game.alive_players()
    wolves = [p for p in alive if p.role == "wolf"]
    wolf_targets = [p for p in alive if p.role != "wolf"]

    for w in wolves:
        kb = [[InlineKeyboardButton(p.name, callback_data=f"ww_kill_{chat_id}_{p.id}")] for p in wolf_targets]
        try:
            await context.bot.send_message(w.id, "🐺 امشب کی رو می‌کشید؟", reply_markup=InlineKeyboardMarkup(kb))
        except Forbidden:
            await context.bot.send_message(chat_id, f"⚠️ نتونستم به {w.name} پیام خصوصی بدم.")

    seer = next((p for p in alive if p.role == "seer"), None)
    if seer:
        targets = [p for p in alive if p.id != seer.id]
        kb = [[InlineKeyboardButton(p.name, callback_data=f"ww_seer_{chat_id}_{p.id}")] for p in targets]
        try:
            await context.bot.send_message(seer.id, "🔮 کی رو می‌خوای چک کنی؟", reply_markup=InlineKeyboardMarkup(kb))
        except Forbidden:
            await context.bot.send_message(chat_id, f"⚠️ نتونستم به {seer.name} پیام خصوصی بدم.")

    doctor = next((p for p in alive if p.role == "doctor"), None)
    if doctor:
        kb = [[InlineKeyboardButton(p.name, callback_data=f"ww_save_{chat_id}_{p.id}")] for p in alive]
        try:
            await context.bot.send_message(doctor.id, "💉 امشب کی رو نجات می‌دی؟", reply_markup=InlineKeyboardMarkup(kb))
        except Forbidden:
            await context.bot.send_message(chat_id, f"⚠️ نتونستم به {doctor.name} پیام خصوصی بدم.")

    waited = 0
    while waited < WW_NIGHT_SECONDS:
        await asyncio.sleep(2)
        waited += 2
        wolves_done = all(w.id in game.night_kill_votes for w in wolves) if wolves else True
        seer_done = (seer is None) or game.seer_acted
        doctor_done = (doctor is None) or (game.doctor_save is not None)
        if wolves_done and seer_done and doctor_done:
            break

    ww_resolve_night(game)


def ww_resolve_night(game: "WWGame"):
    votes = list(game.night_kill_votes.values())
    victim_id = None
    if votes:
        tally = {}
        for v in votes:
            tally[v] = tally.get(v, 0) + 1
        top_count = max(tally.values())
        top = [k for k, c in tally.items() if c == top_count]
        victim_id = random.choice(top)
    game.last_victim_id = victim_id
    game.last_saved = victim_id is not None and victim_id == game.doctor_save


async def ww_run_day(chat_id, context: ContextTypes.DEFAULT_TYPE):
    game = ww_games[chat_id]
    game.state = "day_discuss"

    victim_id = game.last_victim_id
    if victim_id and not game.last_saved:
        victim = game.players[victim_id]
        victim.alive = False
        await context.bot.send_message(
            chat_id, f"☀️ صبح شد... متأسفانه {victim.name} ({WW_ROLE_FA[victim.role]}) دیشب کشته شد. 💀"
        )
    elif victim_id and game.last_saved:
        await context.bot.send_message(chat_id, "☀️ صبح شد... دیشب یه نفر هدف گرگ‌ها بود ولی دکتر نجاتش داد! 🎉")
    else:
        await context.bot.send_message(chat_id, "☀️ صبح شد... دیشب اتفاق خاصی نیفتاد.")

    winner = ww_check_win(game)
    if winner:
        return winner

    await context.bot.send_message(chat_id, f"💬 {WW_DAY_DISCUSSION_SECONDS} ثانیه وقت دارید صحبت کنید و گرگ‌ها رو پیدا کنید...")
    await asyncio.sleep(WW_DAY_DISCUSSION_SECONDS)

    game.state = "day_vote"
    game.day_votes = {}
    alive = game.alive_players()
    kb = [[InlineKeyboardButton(p.name, callback_data=f"ww_vote_{chat_id}_{p.id}")] for p in alive]
    await context.bot.send_message(chat_id, "🗳️ رأی‌گیری! کی رو می‌خواید اعدام کنید؟", reply_markup=InlineKeyboardMarkup(kb))

    waited = 0
    while waited < WW_VOTE_SECONDS:
        await asyncio.sleep(2)
        waited += 2
        if len(game.day_votes) >= len(alive):
            break

    text = ww_resolve_vote(game)
    await context.bot.send_message(chat_id, text)
    return ww_check_win(game)


def ww_resolve_vote(game: "WWGame") -> str:
    votes = list(game.day_votes.values())
    if not votes:
        return "🤷 هیچ‌کس رأی نداد، امروز کسی اعدام نشد."
    tally = {}
    for v in votes:
        tally[v] = tally.get(v, 0) + 1
    top_count = max(tally.values())
    top = [k for k, c in tally.items() if c == top_count]
    if len(top) > 1:
        return "⚖️ رأی‌ها مساوی شد، امروز کسی اعدام نشد."
    target_id = top[0]
    target = game.players[target_id]
    target.alive = False
    return f"⚖️ رأی گروه: {target.name} اعدام شد. نقشش {WW_ROLE_FA[target.role]} بود!"


async def ww_announce_winner(chat_id, context: ContextTypes.DEFAULT_TYPE, winner: str):
    game = ww_games[chat_id]
    reveal = "\n".join(f"• {p.name}: {WW_ROLE_FA[p.role]}" for p in game.players.values())
    text = "🎉 روستایی‌ها بردن و همه‌ی گرگ‌ها رو پیدا کردن!" if winner == "village" else "🐺 گرگ‌ها بردن و روستا رو تصرف کردن!"
    await context.bot.send_message(chat_id, f"{text}\n\n🎭 نقش همه:\n{reveal}")


async def gorgineh_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat = update.effective_chat
    if chat.type == "private":
        await update.message.reply_text("🐺 این بازی فقط توی گروه قابل اجراست.")
        return
    await ww_start_lobby(chat.id, update.effective_user.id, context)


async def startgame_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        await update.message.reply_text("⛔ فقط ادمین می‌تونه زودتر بازی رو شروع کنه.")
        return
    chat_id = update.effective_chat.id
    game = ww_games.get(chat_id)
    if not game or game.state != "lobby":
        await update.message.reply_text("لابی‌ای برای شروع نیست. اول با /gorgineh یکی بساز.")
        return
    await ww_try_start_game(chat_id, context)


async def endgame_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if not await is_admin(update, context):
        await update.message.reply_text("⛔ فقط ادمین می‌تونه بازی رو لغو کنه.")
        return
    chat_id = update.effective_chat.id
    if chat_id in ww_games:
        ww_cleanup_game(chat_id)
        await update.message.reply_text("🛑 بازی گرگینه لغو شد.")
    else:
        await update.message.reply_text("بازی‌ای در جریان نیست.")


async def players_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.effective_chat.id
    game = ww_games.get(chat_id)
    if not game:
        await update.message.reply_text("بازی‌ای در جریان نیست.")
        return
    lines = [f"👥 بازیکنان ({len(game.players)} نفر):"]
    for p in game.players.values():
        lines.append(f"{'🟢' if p.alive else '💀'} {p.name}")
    await update.message.reply_text("\n".join(lines))


async def ww_button_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    try:
        await query.answer()
    except Exception:
        pass

    data = query.data
    user = query.from_user

    if data == "ww_join":
        chat_id = query.message.chat_id
        game = ww_games.get(chat_id)
        if not game or game.state != "lobby":
            await query.message.reply_text("لابی‌ای برای پیوستن نیست.")
            return
        if user.id in game.players:
            await query.message.reply_text(f"{user.first_name} جان، تو از قبل عضو بازی هستی!")
            return
        if len(game.players) >= WW_MAX_PLAYERS:
            await query.message.reply_text("ظرفیت بازی پره!")
            return
        game.players[user.id] = WWPlayer(user)
        ww_player_game[user.id] = chat_id
        await context.bot.send_message(chat_id, f"✅ {user.first_name} به بازی پیوست. ({len(game.players)} نفر)")
        return

    # نکته‌ی مهم (رفع باگ): برای اکشن‌های شبانه/رأی‌گیری، chat_id مستقیماً از خودِ
    # callback_data خونده می‌شه (نه از یه دیکشنری سراسری بر اساس آخرین بازیِ کاربر).
    # این‌جوری اگه یه کاربر همزمان عضو دو بازی توی دو گروه مختلف باشه، اکشن‌هاش
    # هیچ‌وقت با هم قاطی نمی‌شن.
    try:
        parts = data.split("_")
        action = parts[1]  # kill / seer / save / vote
        chat_id = int(parts[2])
        target_id = int(parts[3])
    except (IndexError, ValueError):
        await query.message.reply_text("⚠️ این دکمه دیگه معتبر نیست.")
        return

    game = ww_games.get(chat_id)
    if not game:
        await query.message.reply_text("این بازی دیگه فعال نیست.")
        return
    if user.id not in game.players:
        await query.message.reply_text("تو عضو این بازی نیستی.")
        return
    if target_id not in game.players:
        await query.message.reply_text("⚠️ این بازیکن دیگه توی بازی نیست.")
        return

    player = game.players[user.id]
    if not player.alive:
        await query.message.reply_text("تو دیگه توی این دور بازی نیستی (مرده‌ای)! 💀")
        return

    try:
        if action == "kill":
            if player.role != "wolf" or game.state != "night":
                await query.message.reply_text("⚠️ الان نوبت اکشن تو نیست.")
                return
            game.night_kill_votes[user.id] = target_id
            await query.message.reply_text(f"✅ رأیت ثبت شد: {game.players[target_id].name}")
        elif action == "seer":
            if player.role != "seer" or game.state != "night":
                await query.message.reply_text("⚠️ الان نوبت اکشن تو نیست.")
                return
            target = game.players[target_id]
            game.seer_acted = True
            await query.message.reply_text(f"🔮 نتیجه: {target.name} {'گرگه! 🐺' if target.role == 'wolf' else 'گرگ نیست. ✅'}")
        elif action == "save":
            if player.role != "doctor" or game.state != "night":
                await query.message.reply_text("⚠️ الان نوبت اکشن تو نیست.")
                return
            game.doctor_save = target_id
            await query.message.reply_text(f"✅ ثبت شد: امشب {game.players[target_id].name} رو نجات می‌دی.")
        elif action == "vote":
            if game.state != "day_vote":
                await query.message.reply_text("⚠️ الان زمان رأی‌گیری نیست.")
                return
            game.day_votes[user.id] = target_id
            await query.message.reply_text("🗳️ رأیت ثبت شد.")
        else:
            await query.message.reply_text("⚠️ دکمه‌ی نامعتبر.")
    except (KeyError, IndexError, ValueError) as e:
        logger.warning(f"خطای دکمه گرگینه: {e}")
        await query.message.reply_text("⚠️ یه مشکل موقتی پیش اومد.")


# ============================================================
# مدیریت خطای کلی (تا ربات هیچ‌وقت کرش نکنه)
# ============================================================
async def error_handler(update, context: ContextTypes.DEFAULT_TYPE):
    logger.error("خطای پیش‌بینی‌نشده:\n" + "".join(traceback.format_exception(type(context.error), context.error, context.error.__traceback__)))


def main():
    if not BOT_TOKEN:
        raise SystemExit("متغیر محیطی BOT_TOKEN تنظیم نشده. با export BOT_TOKEN=... مقداردهیش کن.")
    app = ApplicationBuilder().token(BOT_TOKEN).build()

    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("fal", fal_cmd))
    app.add_handler(CommandHandler("tarot", tarot_cmd))
    app.add_handler(CommandHandler("hafez", hafez_cmd))
    app.add_handler(CommandHandler("shans", shans_cmd))
    app.add_handler(CommandHandler("eightball", eightball_cmd))
    app.add_handler(CommandHandler("wheel", wheel_cmd))
    app.add_handler(CommandHandler("td", td_cmd))
    app.add_handler(CommandHandler("rules", rules_cmd))
    app.add_handler(CommandHandler("dollar", dollar_cmd))
    app.add_handler(CommandHandler("bitcoin", bitcoin_cmd))
    app.add_handler(CommandHandler("price", price_cmd))
    app.add_handler(CommandHandler("id", id_cmd))
    app.add_handler(CommandHandler("stats", stats_cmd))
    app.add_handler(CommandHandler("report", report_cmd))
    app.add_handler(CommandHandler("botstatus", botstatus_cmd))
    app.add_handler(CommandHandler("adminpanel", adminpanel_cmd))

    app.add_handler(CommandHandler("joke", joke_cmd))
    app.add_handler(CommandHandler("quote", quote_cmd))
    app.add_handler(CommandHandler("compliment", compliment_cmd))
    app.add_handler(CommandHandler("roast", roast_cmd))
    app.add_handler(CommandHandler("rps", rps_cmd))
    app.add_handler(CommandHandler("coin", coin_cmd))
    app.add_handler(CommandHandler("dice", dice_cmd))
    app.add_handler(CommandHandler("love", love_cmd))

    app.add_handler(CommandHandler("gorgineh", gorgineh_cmd))
    app.add_handler(CommandHandler("startgame", startgame_cmd))
    app.add_handler(CommandHandler("endgame", endgame_cmd))
    app.add_handler(CommandHandler("players", players_cmd))
    app.add_handler(CallbackQueryHandler(ww_button_handler, pattern=r"^ww_"))

    app.add_handler(CommandHandler("addbad", addbad_cmd))
    app.add_handler(CommandHandler("removebad", removebad_cmd))
    app.add_handler(CommandHandler("listbad", listbad_cmd))

    app.add_handler(CommandHandler("mute", mute_cmd))
    app.add_handler(CommandHandler("unmute", unmute_cmd))
    app.add_handler(CommandHandler("kick", kick_cmd))
    app.add_handler(CommandHandler("ban", ban_cmd))
    app.add_handler(CommandHandler("warn", warn_cmd))
    app.add_handler(CommandHandler("pin", pin_cmd))
    app.add_handler(CommandHandler("unpin", unpin_cmd))
    app.add_handler(CommandHandler("purge", purge_cmd))

    # نکته: هندلر بدون pattern (button_handler) باید بعد از هندلر ww_ ثبت بشه که با
    # pattern محدود شده، تا هیچ تداخلی توی دکمه‌های بازی گرگینه پیش نیاد.
    app.add_handler(CallbackQueryHandler(button_handler))
    app.add_handler(MessageHandler(filters.StatusUpdate.NEW_CHAT_MEMBERS, welcome_new_member))
    app.add_handler(MessageHandler(filters.StatusUpdate.LEFT_CHAT_MEMBER, member_left))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_group_text))

    app.add_error_handler(error_handler)
    app.post_init = set_commands

    # فعال‌سازی جاب زمان‌بندی‌شده‌ی یادآور - هر ۶۰ ثانیه چک می‌کنه
    if app.job_queue is not None:
        app.job_queue.run_repeating(reminder_check_job, interval=60, first=5)
    else:
        logger.warning(
            "JobQueue در دسترس نیست - برای فعال شدن قابلیت یادآور خودکار، پکیج رو با "
            "'pip install \"python-telegram-bot[job-queue]\"' نصب کن."
        )

    print("✅ دستیار هوشمند روشن شد و در حال اجراست...")
    app.run_polling(drop_pending_updates=True)


async def set_commands(app):
    commands = [
        BotCommand("start", "منوی اصلی"),
        BotCommand("fal", "فال روزانه"),
        BotCommand("tarot", "کارت تاروت"),
        BotCommand("hafez", "فال حافظ"),
        BotCommand("shans", "درصد شانس امروز"),
        BotCommand("eightball", "توپ جادویی هشت"),
        BotCommand("wheel", "چرخ شانس"),
        BotCommand("td", "جرأت یا حقیقت"),
        BotCommand("joke", "یه جوک بامزه"),
        BotCommand("quote", "یه ضرب‌المثل"),
        BotCommand("compliment", "تعریف بامزه از یه نفر (ریپلای کن)"),
        BotCommand("roast", "متلک بامزه و دوستانه (ریپلای کن)"),
        BotCommand("rps", "سنگ کاغذ قیچی"),
        BotCommand("coin", "شیر یا خط"),
        BotCommand("dice", "پرتاب تاس"),
        BotCommand("love", "عشق‌سنج شوخی"),
        BotCommand("gorgineh", "شروع بازی گروهی گرگینه"),
        BotCommand("startgame", "شروع زودهنگام گرگینه - فقط ادمین"),
        BotCommand("endgame", "لغو بازی گرگینه - فقط ادمین"),
        BotCommand("players", "لیست بازیکنان گرگینه"),
        BotCommand("dollar", "قیمت دلار"),
        BotCommand("bitcoin", "قیمت بیت‌کوین"),
        BotCommand("price", "قیمت دلار و بیت‌کوین"),
        BotCommand("rules", "قوانین گروه"),
        BotCommand("stats", "آمار گروه"),
        BotCommand("botstatus", "وضعیت و دسترسی‌های ربات توی گروه"),
        BotCommand("adminpanel", "پنل مدیریت شیشه‌ای (الفاظ + یادآور خودکار) - فقط ادمین"),
        BotCommand("report", "گزارش پیام به ادمین (ریپلای کن)"),
        BotCommand("id", "دیدن آیدی عددی"),
        BotCommand("mute", "سکوت عضو - فقط ادمین (ریپلای کن)"),
        BotCommand("unmute", "باز کردن سکوت - فقط ادمین (ریپلای کن)"),
        BotCommand("kick", "اخراج عضو - فقط ادمین (ریپلای کن)"),
        BotCommand("ban", "بن عضو - فقط ادمین (ریپلای کن)"),
        BotCommand("warn", "اخطار به عضو - فقط ادمین (ریپلای کن)"),
        BotCommand("pin", "پین کردن پیام - فقط ادمین (ریپلای کن)"),
        BotCommand("unpin", "برداشتن پین - فقط ادمین"),
        BotCommand("purge", "پاک کردن N پیام اخیر - فقط ادمین"),
        BotCommand("addbad", "افزودن کلمه فیلتر - فقط ادمین"),
        BotCommand("removebad", "حذف کلمه فیلتر - فقط ادمین"),
        BotCommand("listbad", "تعداد کلمات فیلترشده - فقط ادمین"),
    ]
    await app.bot.set_my_commands(commands)


if __name__ == "__main__":
    main()
