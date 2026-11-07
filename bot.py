"""Rasmlarni PDF'ga aylantiruvchi va test savollaridan quiz yasovchi Telegram bot.

1) Rasmlar -> PDF: foydalanuvchi 50 tagacha rasm yuboradi, "PDF yaratish" tugmasini bosadi.
2) Quiz: foydalanuvchi test savollarini matn (yoki .txt fayl) qilib yuboradi,
   bot ularni Telegram'ning quiz so'rovnomalariga aylantirib yuboradi va oxirida
   bitta ulashish havolasini beradi. Havolani olgan odam botga kirib Start bosadi
   va quizni o'z chatida yoki guruhda ishlaydi.

Quizlarni doimiy saqlash uchun GitHub Gist ishlatiladi (GITHUB_TOKEN muhit
o'zgaruvchisi kerak). Token yo'q bo'lsa, havola funksiyasi o'chiq turadi,
qolgan hamma narsa ishlayveradi.

Token kod ichiga yozilmaydi: u BOT_TOKEN muhit o'zgaruvchisidan olinadi.

Render'da ishlaganda bot webhook rejimida ishlaydi (Render bergan manzil
RENDER_EXTERNAL_URL orqali olinadi). Kompyuteringizda sinab ko'rsangiz,
RENDER_EXTERNAL_URL bo'lmagani uchun oddiy polling rejimi ishlaydi.
"""

import asyncio
import hashlib
import json
import logging
import os
import re
import tempfile
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path

from PIL import Image, ImageOps
from telegram import (
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    Poll,
    ReplyKeyboardMarkup,
    Update,
)
from telegram.error import RetryAfter
from telegram.ext import (
    Application,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

MAX_IMAGES = 50
MAX_PDF_BYTES = 49 * 1024 * 1024  # Telegram botlari 50 MB gacha fayl yubora oladi
MAX_SIDE = (1240, 1754)  # A4 sahifa, taxminan 150 dpi
JPEG_QUALITY = 85

MAX_QUESTIONS = 100  # bir marta yuborilganda eng ko'pi bilan nechta quiz
MAX_QUESTION_LEN = 300  # Telegram quiz savoli uzunligi chegarasi
MAX_OPTION_LEN = 100  # Telegram variant uzunligi chegarasi
MAX_TXT_BYTES = 1_000_000

GIST_API = "https://api.github.com"
QUIZ_ID_RE = re.compile(r"^[0-9a-f]{20,40}$")
START_PREFIX = "q_"  # havoladagi start parametri: q_<quiz id> (Telegram chegarasi: 64 belgi)
POLL_DELAY_PRIVATE = 0.6
POLL_DELAY_GROUP = 3.2  # guruhlarda Telegram daqiqasiga taxminan 20 xabarga ruxsat beradi

# Doim ko'rinib turadigan tugmalar
BTN_PDF = "📄 PDF yaratish"
BTN_QUIZ = "📝 Quiz yaratish"
BTN_CLEAR = "🗑 Tozalash"
BTN_HELP = "ℹ️ Yordam"
KEYBOARD = ReplyKeyboardMarkup(
    [[BTN_PDF, BTN_QUIZ], [BTN_CLEAR, BTN_HELP]],
    resize_keyboard=True,
    is_persistent=True,
)

logging.basicConfig(
    format="%(asctime)s %(levelname)s %(name)s: %(message)s", level=logging.INFO
)
logger = logging.getLogger(__name__)


# ---------------------------------------------------------------------------
# Rasmlar -> PDF
# ---------------------------------------------------------------------------

def get_files(context: ContextTypes.DEFAULT_TYPE) -> list:
    return context.user_data.setdefault("files", [])


def build_pdf(paths: list, out_path: Path) -> None:
    """Rasmlarni ketma-ket bitta PDF faylga yig'adi.

    Har bir rasm avval kichraytirilib vaqtinchalik JPEG qilib saqlanadi,
    shunda 50 ta rasm ham xotirani (Render'ning bepul 512 MB) to'ldirib yubormaydi.
    """
    work = out_path.parent
    jpgs = []
    for i, p in enumerate(paths):
        with Image.open(p) as img:
            img = ImageOps.exif_transpose(img)  # telefon rasmlarining yo'nalishini to'g'rilaydi
            img = img.convert("RGB")
            img.thumbnail(MAX_SIDE)
            jpg = work / f"page_{i:03d}.jpg"
            img.save(jpg, "JPEG", quality=JPEG_QUALITY)
        jpgs.append(jpg)

    pages = [Image.open(j) for j in jpgs]
    try:
        pages[0].save(
            out_path,
            "PDF",
            save_all=True,
            append_images=pages[1:],
            resolution=150.0,
        )
    finally:
        for page in pages:
            page.close()


# ---------------------------------------------------------------------------
# Matndan quiz savollarini ajratib olish
# ---------------------------------------------------------------------------

# Variant harflari: lotin A-F va kirill А-Е (hamda lotinga o'xshash kirill С).
_LABEL_CHARS = "ABCDEFabcdefАБВГДЕабвгдеСс"
# Lotinga o'xshash kirill harflarini lotinga o'giramiz (А, В, Е, С): "В" va "B" bir xil bo'lib qoladi.
_LOOKALIKE = str.maketrans(
    "АВЕСавес", "ABECabec"
)

_OPTION_RE = re.compile(
    r"^\s*(?P<mark>[*+✅✔]️?\s*)?\(?(?P<label>[" + _LABEL_CHARS + r"])\s*[\).:]\s*(?P<text>\S.*?)\s*$"
)
_ANSWER_RE = re.compile(
    r"^\s*(?:to.?g.?ri(?:\s+javob)?|javob|answer|ans|ответ"
    r"|жавоб|тўғри)"
    r"\s*[:=\-–]?\s*\(?(?P<ans>[A-Za-zЀ-ӿ]|\d{1,2})(?=$|[\s\).:,])",
    re.IGNORECASE,
)
_NUM_RE = re.compile(r"^\s*(?:savol\s*)?(?:№\s*)?\d{1,3}\s*[\).:]\s+", re.IGNORECASE)


def _norm(label: str) -> str:
    return label.translate(_LOOKALIKE).upper()


def parse_quiz(text: str):
    """Matndan savollarni ajratadi. (savollar, xatolar) qaytaradi.

    Savol: {"question": str, "options": [str], "correct": int}
    Qo'llab-quvvatlanadigan format:
        1. Savol matni?
        A) variant
        B) variant
        Javob: B
    yoki to'g'ri variant oldiga * yoki + qo'yiladi:
        *B) variant
    """
    questions, errors = [], []
    cur = None

    def new():
        return {"q": [], "opts": [], "labels": [], "marked": None, "answer": None}

    def finish():
        nonlocal cur
        if cur is None:
            return
        c, cur = cur, None
        if not c["opts"]:
            return  # variantsiz matn: oddiy gap, savol emas
        q = _NUM_RE.sub("", " ".join(c["q"]).strip(), count=1).strip()
        title = (q[:40] + "…") if len(q) > 40 else (q or "(savol matni yo'q)")

        if not q:
            errors.append(f"{title}: savol matni topilmadi")
            return
        if not 2 <= len(c["opts"]) <= 10:
            errors.append(f"{title}: variantlar soni 2 dan 10 gacha bo'lishi kerak")
            return
        if any(len(o) > MAX_OPTION_LEN for o in c["opts"]):
            errors.append(f"{title}: variant {MAX_OPTION_LEN} belgidan uzun")
            return

        idx = None
        if c["marked"] is not None:
            idx = c["marked"]
        elif c["answer"] is not None:
            ans = c["answer"]
            if ans.isdigit():
                idx = int(ans) - 1
            elif _norm(ans) in c["labels"]:
                idx = c["labels"].index(_norm(ans))
        if idx is None or not 0 <= idx < len(c["opts"]):
            errors.append(f"{title}: to'g'ri javob ko'rsatilmagan yoki noto'g'ri")
            return

        questions.append({"question": q, "options": c["opts"], "correct": idx})

    for raw in text.splitlines():
        line = raw.strip()
        if not line:
            continue

        m_ans = _ANSWER_RE.match(line)
        if m_ans and cur is not None and cur["opts"]:
            cur["answer"] = m_ans.group("ans")
            finish()
            continue

        m_opt = _OPTION_RE.match(line)
        if m_opt:
            if cur is None:
                cur = new()
            if m_opt.group("mark") and cur["marked"] is None:
                cur["marked"] = len(cur["opts"])
            cur["labels"].append(_norm(m_opt.group("label")))
            cur["opts"].append(m_opt.group("text"))
            continue

        # Oddiy matn qatori: yangi savol boshlanishi yoki savolning davomi
        if cur is not None and cur["opts"]:
            finish()
        if cur is None:
            cur = new()
        cur["q"].append(line)

    finish()
    return questions, errors


QUIZ_FORMAT = (
    "Savollarni shu ko'rinishda yuboring (bir nechtasini ketma-ket yozsangiz bo'ladi):\n\n"
    "1. O'zbekiston poytaxti qaysi shahar?\n"
    "A) Samarqand\n"
    "B) Toshkent\n"
    "C) Buxoro\n"
    "D) Xiva\n"
    "Javob: B\n\n"
    "2. 2 + 2 nechiga teng?\n"
    "A) 3\n"
    "*B) 4\n"
    "C) 5\n\n"
    "To'g'ri javobni \"Javob: B\" deb yoki to'g'ri variant oldiga * (yoki +) qo'yib ko'rsatasiz. "
    "Matnni xabar qilib yoki .txt fayl qilib yuborishingiz mumkin.\n\n"
    "Quiz yuborilgach, uni boshqalarga ulashish uchun havola ham beriladi."
)


# ---------------------------------------------------------------------------
# Quizni doimiy saqlash (GitHub Gist) va ulashish havolasi
# ---------------------------------------------------------------------------

_quiz_cache = {}


def storage_enabled() -> bool:
    return bool(os.environ.get("GITHUB_TOKEN"))


def _gist_request(method: str, path: str, body=None):
    headers = {
        "Accept": "application/vnd.github+json",
        "User-Agent": "telegram-quiz-bot",
        "X-GitHub-Api-Version": "2022-11-28",
    }
    token = os.environ.get("GITHUB_TOKEN")
    if token:
        headers["Authorization"] = f"Bearer {token}"
    data = None
    if body is not None:
        data = json.dumps(body).encode("utf-8")
        headers["Content-Type"] = "application/json"
    req = urllib.request.Request(f"{GIST_API}{path}", data=data, headers=headers, method=method)
    with urllib.request.urlopen(req, timeout=20) as resp:
        return json.loads(resp.read().decode("utf-8"))


def _remember(quiz_id: str, questions: list) -> None:
    if len(_quiz_cache) >= 200:
        _quiz_cache.pop(next(iter(_quiz_cache)))
    _quiz_cache[quiz_id] = questions


def _save_quiz_sync(questions: list) -> str:
    content = json.dumps({"v": 1, "questions": questions}, ensure_ascii=False, separators=(",", ":"))
    resp = _gist_request(
        "POST",
        "/gists",
        {
            "description": "Telegram quiz",
            "public": False,  # maxfiy gist: faqat havolasini bilgan ochadi
            "files": {"quiz.json": {"content": content}},
        },
    )
    quiz_id = resp["id"]
    if not QUIZ_ID_RE.match(quiz_id):
        raise ValueError("Kutilmagan quiz ID formati")
    _remember(quiz_id, questions)
    return quiz_id


def _validate_questions(data):
    """Saqlangan quiz ma'lumotini tekshiradi; noto'g'ri bo'lsa None qaytaradi."""
    try:
        out = []
        for item in data["questions"][:MAX_QUESTIONS]:
            q, opts, correct = item["question"], item["options"], item["correct"]
            ok = (
                isinstance(q, str)
                and q.strip()
                and isinstance(opts, list)
                and 2 <= len(opts) <= 10
                and all(isinstance(o, str) and 0 < len(o) <= MAX_OPTION_LEN for o in opts)
                and isinstance(correct, int)
                and not isinstance(correct, bool)
                and 0 <= correct < len(opts)
            )
            if not ok:
                return None
            out.append({"question": q, "options": opts, "correct": correct})
        return out or None
    except (KeyError, TypeError):
        return None


def _load_quiz_sync(quiz_id: str):
    if quiz_id in _quiz_cache:
        return _quiz_cache[quiz_id]
    resp = _gist_request("GET", f"/gists/{quiz_id}")
    questions = _validate_questions(json.loads(resp["files"]["quiz.json"]["content"]))
    if questions:
        _remember(quiz_id, questions)
    return questions


async def load_quiz(quiz_id: str):
    if not QUIZ_ID_RE.match(quiz_id):  # manzilga faqat tekshirilgan ID qo'yiladi
        return None
    try:
        return await asyncio.to_thread(_load_quiz_sync, quiz_id)
    except urllib.error.HTTPError as e:
        logger.warning("Quizni yuklab bo'lmadi: HTTP %s", e.code)
        return None
    except Exception:
        logger.exception("Quizni yuklab bo'lmadi")
        return None


def quiz_links(bot_username: str, quiz_id: str):
    payload = START_PREFIX + quiz_id
    return (
        f"https://t.me/{bot_username}?start={payload}",
        f"https://t.me/{bot_username}?startgroup={payload}",
    )


async def _with_retry(fn, **kwargs):
    """Telegram tezlik cheklovi (RetryAfter) chiqsa, kutib, bir marta qayta urinadi."""
    try:
        return await fn(**kwargs)
    except RetryAfter as e:
        wait = e.retry_after
        wait = wait.total_seconds() if hasattr(wait, "total_seconds") else float(wait)
        await asyncio.sleep(wait + 1)
        return await fn(**kwargs)


async def deliver_polls(bot, chat_id: int, questions: list, delay: float):
    """Savollarni quiz so'rovnomasi qilib chatga yuboradi. (yuborilgan soni, xatolar) qaytaradi."""
    sent, errors = 0, []
    for q in questions:
        question = q["question"]
        try:
            if len(question) > MAX_QUESTION_LEN:
                # Quiz savoli 300 belgidan oshmasligi kerak: uzun savolni alohida xabar qilamiz.
                await _with_retry(bot.send_message, chat_id=chat_id, text=question[:4000])
                question = "Javobni tanlang:"
            await _with_retry(
                bot.send_poll,
                chat_id=chat_id,
                question=question,
                options=q["options"],
                type=Poll.QUIZ,
                correct_option_id=q["correct"],
            )
            sent += 1
        except Exception:
            logger.exception("Quiz yuborishda xatolik")
            errors.append(f"{q['question'][:40]}: yuborib bo'lmadi")
        await asyncio.sleep(delay)  # Telegram tezlik cheklovidan oshib ketmaslik uchun
    return sent, errors


async def send_share_message(msg, bot, quiz_id: str, count: int) -> None:
    private_link, group_link = quiz_links(bot.username, quiz_id)
    share_url = (
        "https://t.me/share/url?url="
        + urllib.parse.quote(private_link, safe="")
        + "&text="
        + urllib.parse.quote(f"Quiz: {count} ta savol. Boshlash uchun havolani bosing.", safe="")
    )
    markup = InlineKeyboardMarkup(
        [
            [InlineKeyboardButton("📨 Havolani yuborish", url=share_url)],
            [InlineKeyboardButton("👥 Guruhga qo'shish", url=group_link)],
        ]
    )
    await msg.reply_text(
        f"🔗 Quiz havolasi ({count} ta savol):\n{private_link}\n\n"
        "Havolani olgan odam botga kiradi, Start bosadi va quizni o'z chatida yoki guruhda ishlaydi.",
        reply_markup=markup,
    )


async def send_quiz(msg, bot, text: str) -> None:
    questions, errors = parse_quiz(text)

    if not questions:
        if errors:
            problems = (
                "Quyidagi savollarni o'qib bo'lmadi:\n"
                + "\n".join("- " + e for e in errors[:10])
                + "\n\n"
            )
        else:
            problems = "Matnda test savollari topilmadi.\n\n"
        await msg.reply_text(problems + QUIZ_FORMAT, reply_markup=KEYBOARD)
        return

    extra = max(0, len(questions) - MAX_QUESTIONS)
    questions = questions[:MAX_QUESTIONS]

    await msg.reply_text(
        f"{len(questions)} ta savol topildi, quiz yuborilmoqda...", reply_markup=KEYBOARD
    )

    sent, send_errors = await deliver_polls(bot, msg.chat_id, questions, POLL_DELAY_PRIVATE)
    errors = errors + send_errors

    parts = [f"Tayyor: {sent} ta quiz yuborildi."]
    if extra:
        parts.append(f"Bir martada {MAX_QUESTIONS} tagacha savol yuboriladi, {extra} tasi qoldi.")
    if errors:
        parts.append("O'tkazib yuborilganlar:\n" + "\n".join("- " + e for e in errors[:10]))
        if len(errors) > 10:
            parts.append(f"... va yana {len(errors) - 10} ta.")
    await msg.reply_text("\n\n".join(parts), reply_markup=KEYBOARD)

    # Hammasini bitta ulashish havolasiga birlashtiramiz
    if sent and storage_enabled():
        try:
            quiz_id = await asyncio.to_thread(_save_quiz_sync, questions)
            await send_share_message(msg, bot, quiz_id, len(questions))
        except Exception:
            logger.exception("Quiz havolasini yaratib bo'lmadi")
            await msg.reply_text(
                "Quiz havolasini yaratib bo'lmadi. Birozdan keyin qayta urinib ko'ring.",
                reply_markup=KEYBOARD,
            )
    elif sent:
        logger.info("GITHUB_TOKEN berilmagan: quiz havolasi yaratilmadi")


# ---------------------------------------------------------------------------
# Bot buyruqlari, tugmalari va havola orqali ochish
# ---------------------------------------------------------------------------

HELP_TEXT = (
    "Men ikkita ish qila olaman.\n\n"
    f"1) Rasmlarni PDF'ga aylantirish: menga rasmlarni yuboring ({MAX_IMAGES} tagacha), "
    f"keyin \"{BTN_PDF}\" tugmasini bosing. \"{BTN_CLEAR}\" yuborilgan rasmlarni o'chiradi. "
    "Rasmlarni fayl (hujjat) sifatida yuborsangiz, sifati yaxshiroq saqlanadi.\n\n"
    f"2) Test savollaridan quiz yasash: savollarni matn qilib yuboring, oxirida ulashish havolasi beriladi. "
    f"Format uchun \"{BTN_QUIZ}\" tugmasini bosing."
)


def _is_private(update: Update) -> bool:
    chat = update.effective_chat
    return chat is not None and chat.type == "private"


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if context.args and context.args[0].startswith(START_PREFIX):
        await open_quiz(update, context, context.args[0][len(START_PREFIX):])
        return
    await update.message.reply_text(
        "Salom! " + HELP_TEXT, reply_markup=KEYBOARD if _is_private(update) else None
    )


async def open_quiz(update: Update, context: ContextTypes.DEFAULT_TYPE, quiz_id: str) -> None:
    """Quiz havolasi orqali kirgan odamga quizni boshlash tugmasini ko'rsatadi."""
    msg = update.message
    questions = await load_quiz(quiz_id)
    if not questions:
        await msg.reply_text(
            "Bu quiz topilmadi yoki eskirgan. Havolani yuborgan odamdan qayta so'rang."
        )
        return

    n = len(questions)
    buttons = [[InlineKeyboardButton("▶️ Boshlash", callback_data=f"run:{quiz_id}")]]
    if _is_private(update):
        _, group_link = quiz_links(context.bot.username, quiz_id)
        buttons.append([InlineKeyboardButton("👥 Guruhda ishlatish", url=group_link)])
        text = (
            f"📝 Quiz: {n} ta savol.\n\n"
            "\"Boshlash\" ni bosing, savollar shu chatga yuboriladi. "
            "Guruhda ishlatmoqchi bo'lsangiz, \"Guruhda ishlatish\" ni bosib guruhni tanlang."
        )
    else:
        minutes = max(1, round(n * POLL_DELAY_GROUP / 60))
        text = (
            f"📝 Quiz: {n} ta savol.\n\n"
            "\"Boshlash\" ni bosing, savollar shu guruhga yuboriladi "
            f"(Telegram cheklovi sababli taxminan {minutes} daqiqa ketadi)."
        )
    await msg.reply_text(text, reply_markup=InlineKeyboardMarkup(buttons))


async def run_quiz(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """\"Boshlash\" tugmasi bosilganda savollarni shu chatga yuboradi."""
    query = update.callback_query
    quiz_id = query.data.split(":", 1)[1]
    chat = query.message.chat

    running = context.application.bot_data.setdefault("running", set())
    if chat.id in running:
        await query.answer("Savollar hozir yuborilmoqda, biroz kuting.", show_alert=True)
        return
    await query.answer()

    questions = await load_quiz(quiz_id)
    if not questions:
        await context.bot.send_message(
            chat_id=chat.id,
            text="Bu quiz topilmadi yoki eskirgan. Havolani yuborgan odamdan qayta so'rang.",
        )
        return

    running.add(chat.id)
    try:
        delay = POLL_DELAY_PRIVATE if chat.type == "private" else POLL_DELAY_GROUP
        sent, errors = await deliver_polls(context.bot, chat.id, questions, delay)
        text = f"Tayyor: {sent} ta savol yuborildi."
        if errors:
            text += "\n\nYuborib bo'lmaganlar:\n" + "\n".join("- " + e for e in errors[:10])
        await context.bot.send_message(chat_id=chat.id, text=text)
    finally:
        running.discard(chat.id)


async def help_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await update.message.reply_text(HELP_TEXT, reply_markup=KEYBOARD)


async def quiz_help(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await update.message.reply_text(QUIZ_FORMAT, reply_markup=KEYBOARD)


async def quiz_from_text(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await send_quiz(update.message, context.bot, update.message.text or "")


async def quiz_from_file(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    msg = update.message
    doc = msg.document
    if doc.file_size and doc.file_size > MAX_TXT_BYTES:
        await msg.reply_text("Fayl juda katta (1 MB gacha bo'lishi kerak).", reply_markup=KEYBOARD)
        return
    tg_file = await context.bot.get_file(doc.file_id)
    data = bytes(await tg_file.download_as_bytearray())
    try:
        text = data.decode("utf-8-sig")
    except UnicodeDecodeError:
        text = data.decode("cp1251", errors="replace")
    await send_quiz(msg, context.bot, text)


async def add_image(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    msg = update.message
    files = get_files(context)

    if len(files) >= MAX_IMAGES:
        await msg.reply_text(
            f"Chegara to'ldi: {MAX_IMAGES} ta rasm. \"{BTN_PDF}\" ni bosing "
            f"yoki \"{BTN_CLEAR}\" bilan tozalang.",
            reply_markup=KEYBOARD,
        )
        return

    if msg.photo:
        file_id = msg.photo[-1].file_id  # eng katta o'lchamdagisi
    else:
        file_id = msg.document.file_id
    files.append(file_id)

    # Har bir rasmga javob yozmaymiz: albom yuborilganda Telegram cheklovi ishga tushadi.
    if len(files) == 1:
        await msg.reply_text(
            f"Rasm qabul qilindi. Yana yuboring yoki \"{BTN_PDF}\" ni bosing.",
            reply_markup=KEYBOARD,
        )
    elif len(files) == MAX_IMAGES:
        await msg.reply_text(
            f"{MAX_IMAGES} ta rasm to'ldi. Endi \"{BTN_PDF}\" ni bosing.",
            reply_markup=KEYBOARD,
        )


async def make_pdf(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    msg = update.message
    files = get_files(context)

    if not files:
        await msg.reply_text("Avval rasm yuboring.", reply_markup=KEYBOARD)
        return

    await msg.reply_text(
        f"{len(files)} ta rasm PDF'ga aylantirilmoqda, biroz kuting...",
        reply_markup=KEYBOARD,
    )

    try:
        with tempfile.TemporaryDirectory() as tmp:
            paths = []
            for i, file_id in enumerate(list(files)):
                tg_file = await context.bot.get_file(file_id)
                path = Path(tmp) / f"{i:03d}.img"
                await tg_file.download_to_drive(path)
                paths.append(path)

            out = Path(tmp) / "rasmlar.pdf"
            await asyncio.to_thread(build_pdf, paths, out)

            if out.stat().st_size > MAX_PDF_BYTES:
                await msg.reply_text(
                    "PDF juda katta bo'lib ketdi. Rasmlarni kamroq qilib qayta urinib ko'ring.",
                    reply_markup=KEYBOARD,
                )
                return

            with out.open("rb") as f:
                await msg.reply_document(f, filename="rasmlar.pdf", reply_markup=KEYBOARD)

        files.clear()
    except Exception:
        logger.exception("PDF yaratishda xatolik")
        await msg.reply_text(
            f"Xatolik yuz berdi. Rasmlaringiz saqlanib qoldi, \"{BTN_PDF}\" ni qayta bosib ko'ring.",
            reply_markup=KEYBOARD,
        )


async def clear(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    get_files(context).clear()
    await update.message.reply_text(
        "Tozalandi. Yangi rasmlarni yuborishingiz mumkin.", reply_markup=KEYBOARD
    )


async def other_message(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await update.message.reply_text(
        "Rasm yuboring (PDF uchun), test savollarini matn qilib yuboring (quiz uchun) "
        "yoki tugmalardan birini bosing.",
        reply_markup=KEYBOARD,
    )


def main() -> None:
    token = os.environ["BOT_TOKEN"]
    # Uzoq PDF yoki ko'p quiz yuborilayotganda boshqa foydalanuvchilar kutib qolmasligi uchun
    app = Application.builder().token(token).concurrent_updates(True).build()

    # /start hamma joyda ishlaydi (guruhda ham: quiz havolasi shu orqali ochiladi)
    app.add_handler(CommandHandler("start", start))
    app.add_handler(CallbackQueryHandler(run_quiz, pattern=r"^run:[0-9a-f]{20,40}$"))

    # Qolgan hamma narsa faqat shaxsiy chatda: guruhdagi oddiy suhbatga bot aralashmaydi
    private = filters.ChatType.PRIVATE

    # Tugmalar (ular umumiy matn qabul qiluvchidan oldin turishi kerak)
    app.add_handler(MessageHandler(private & filters.Text([BTN_PDF]), make_pdf))
    app.add_handler(MessageHandler(private & filters.Text([BTN_QUIZ]), quiz_help))
    app.add_handler(MessageHandler(private & filters.Text([BTN_CLEAR]), clear))
    app.add_handler(MessageHandler(private & filters.Text([BTN_HELP]), help_cmd))

    app.add_handler(
        MessageHandler(private & (filters.PHOTO | filters.Document.IMAGE), add_image)
    )
    app.add_handler(
        MessageHandler(private & filters.Document.FileExtension("txt"), quiz_from_file)
    )
    app.add_handler(MessageHandler(private & filters.TEXT & ~filters.COMMAND, quiz_from_text))
    app.add_handler(MessageHandler(private & filters.ALL, other_message))

    base_url = os.environ.get("WEBHOOK_URL") or os.environ.get("RENDER_EXTERNAL_URL")
    if base_url:
        # Tokenning o'zini manzilga qo'ymaymiz: undan hosil qilingan maxfiy qism ishlatiladi.
        secret = hashlib.sha256(token.encode()).hexdigest()[:40]
        port = int(os.environ.get("PORT", "10000"))
        logger.info("Webhook rejimi, port %s", port)
        app.run_webhook(
            listen="0.0.0.0",
            port=port,
            url_path=secret,
            webhook_url=f"{base_url.rstrip('/')}/{secret}",
            secret_token=secret,
        )
    else:
        logger.info("Polling rejimi (mahalliy sinov)")
        app.run_polling()


if __name__ == "__main__":
    main()
