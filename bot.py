"""Rasmlarni PDF'ga aylantiruvchi va test savollaridan quiz yasovchi Telegram bot.

1) Rasmlar -> PDF: foydalanuvchi 50 tagacha rasm yuboradi, "PDF yaratish" tugmasini bosadi.
2) Quiz: quiz yaratuvchisi test savollarini matn (yoki .txt / Word .docx fayl) qilib yuboradi va har bir
   savol uchun vaqtni (15, 20 yoki 30 soniya) bir marta belgilaydi. Shundan keyin bot bitta
   ulashish havolasini beradi. Havolani olgan odam botga kirib Start bosadi va quizni o'z chatida
   yoki guruhda ishlaydi: undan vaqt so'ralmaydi, quiz yaratuvchi belgilagan vaqt bilan ochiladi.
   Savollar birin-ketin yuboriladi, har biri belgilangan soniya ochiq turadi.
   Guruhda natijalar ochiq: kim qaysi variantni tanlagani hammaga ko'rinadi, va quiz tugagach
   natijalar o'rinlari hamda to'g'ri javoblar soni bilan guruhda e'lon qilinadi.

Quizlarni doimiy saqlash uchun GitHub Gist ishlatiladi (GITHUB_TOKEN muhit
o'zgaruvchisi kerak). Token yo'q bo'lsa, havola funksiyasi o'chiq turadi,
qolgan hamma narsa ishlayveradi.

Token kod ichiga yozilmaydi: u BOT_TOKEN muhit o'zgaruvchisidan olinadi.

OWNER_ID (ixtiyoriy): bot egasining Telegram ID raqami. Berilsa, kimdir botga Start bosganda
egasiga uning ismi, niki (@username) va ID raqami yuboriladi. Raqamni botdagi /myid orqali bilasiz.

Render'da ishlaganda bot webhook rejimida ishlaydi (Render bergan manzil
RENDER_EXTERNAL_URL orqali olinadi). Kompyuteringizda sinab ko'rsangiz,
RENDER_EXTERNAL_URL bo'lmagani uchun oddiy polling rejimi ishlaydi.
"""

import asyncio
import hashlib
import io
import json
import logging
import os
import re
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid
import xml.etree.ElementTree as ET
import zipfile
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
    PollAnswerHandler,
    filters,
)

MAX_IMAGES = 50
MAX_PDF_BYTES = 49 * 1024 * 1024  # Telegram botlari 50 MB gacha fayl yubora oladi
MAX_SIDE = (1240, 1754)  # A4 sahifa, taxminan 150 dpi
JPEG_QUALITY = 85

MAX_QUESTIONS = 1000  # bir marta qabul qilinadigan savollarning eng ko'p soni
SPLIT_CHOICES = (25, 50, 100, 200)  # bitta havolaga sig'adigan savollar soni (tugmalar)
MIN_CHUNK = 5  # qo'lda yozilganda bitta havoladagi eng kam savol
MAX_MISTAKE_USERS = 2000  # xotirada xatolari saqlanadigan foydalanuvchilar soni
IDLE_LIMIT = 3  # ketma-ket shuncha savolga hech kim javob bermasa, quiz to'xtaydi
MAX_PENDING = 50  # xotirada kutayotgan (hali havolasi yaratilmagan) quizlar soni
GIST_MAX_BYTES = 900_000  # bitta Gist fayli hajmi chegarasi (GitHub 1 MB dan kattasini to'liq bermaydi)
MAX_QUESTION_LEN = 300  # Telegram quiz savoli uzunligi chegarasi
MAX_OPTION_LEN = 100  # Telegram variant uzunligi chegarasi
MAX_TXT_BYTES = 1_000_000
MAX_DOCX_BYTES = 10_000_000  # Word fayl (rasmlari bilan) hajmi
MAX_XML_BYTES = 8_000_000  # Word ichidagi matn qismining ochilgan hajmi

TIME_CHOICES = (15, 20, 30)  # har bir savol uchun tanlanadigan soniyalar
DEFAULT_SECONDS = 20  # vaqti belgilanmagan eski quizlar uchun
RESULT_GRACE = 3  # oxirgi savoldan keyin natijalarni e'lon qilishdan oldingi kutish (soniya)
MAX_RESULT_ROWS = 40  # e'londa ko'rsatiladigan ishtirokchilar soni (Telegram xabar uzunligi chegarasi)
KEEP_AWAKE_SECONDS = 240  # quiz davomida bot uxlab qolmasligi uchun o'ziga so'rov yuborish oralig'i

GIST_API = "https://api.github.com"
QUIZ_ID_RE = re.compile(r"^[0-9a-f]{20,40}$")
START_PREFIX = "q_"  # havoladagi start parametri: q_<quiz id> (Telegram chegarasi: 64 belgi)

# Doim ko'rinib turadigan tugmalar
BTN_PDF = "📄 PDF yaratish"
BTN_QUIZ = "📝 Quiz yaratish"
BTN_CLEAR = "🗑 Tozalash"
BTN_HELP = "ℹ️ Yordam"
BTN_GEN = "🎓 Slayd / Referat"
KEYBOARD = ReplyKeyboardMarkup(
    [[BTN_PDF, BTN_QUIZ], [BTN_GEN], [BTN_CLEAR, BTN_HELP]],
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
    r"^\s*(?P<mark>[*+#✅✔]️?\s*)?\(?(?P<label>[" + _LABEL_CHARS + r"])\s*[\).:]\s*(?P<text>\S.*?)\s*$"
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


_SEP_Q_RE = re.compile(r"^\s*\+{3,}\s*(?P<rest>.*)$")  # savollar orasidagi ++++
_SEP_V_RE = re.compile(r"^\s*={3,}\s*(?P<rest>.*)$")  # variantlar orasidagi ====
_DECOR_PREFIX_RE = re.compile(r"^\s*[*#~_\-]{3,}\s*(?P<rest>.*)$")  # ****, ----, #### kabi bezaklar
_DECOR_ONLY_RE = re.compile(r"^[\W_]{3,}$")  # faqat belgilardan iborat qator
_MARK_RE = re.compile(r"^\s*(?:#|[✅✔]️?)\s*")  # harfsiz variant oldidagi "to'g'ri" belgisi
_OPTION_STRICT_RE = re.compile(
    r"^\(?(?P<label>[" + _LABEL_CHARS + r"])\s*[\).:]\s+(?P<text>\S.*?)\s*$"
)


def parse_quiz(text: str):
    """Matndan savollarni ajratadi. (savollar, xatolar) qaytaradi.

    Savol: {"question": str, "options": [str], "correct": int}

    1) Harfli format:
        1. Savol matni?
        A) variant
        B) variant
        Javob: B
       To'g'ri variant oldiga *, + yoki # qo'yish ham mumkin:  #B) variant

    2) Belgili format (harflar shart emas):
        ++++
        Savol matni?
        ====
        variant
        ====
        #to'g'ri variant

    Sarlavha (institut nomi va h.k.) va ++++, ====, ----, **** kabi bezak belgilari
    savolga qo'shilmaydi: raqamlangan savoldan oldingi matn yoki bo'sh qatordan oldingi
    matn sarlavha deb tashlab yuboriladi.
    """
    questions, errors = [], []
    cur = None

    def new():
        return {
            "q": [], "opts": [], "labels": [], "marked": None, "answer": None,
            "blank": False, "delim": False, "await": False,
        }

    def finish():
        nonlocal cur
        if cur is None:
            return
        c, cur = cur, None
        if not c["opts"]:
            return  # variantsiz matn: sarlavha yoki oddiy gap, savol emas
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
            else:
                a = _norm(ans)
                if a in c["labels"]:
                    idx = c["labels"].index(a)
                elif len(a) == 1 and "A" <= a <= "J":
                    idx = ord(a) - ord("A")  # harfsiz variantlar: B = ikkinchi variant
        if idx is None or not 0 <= idx < len(c["opts"]):
            errors.append(f"{title}: to'g'ri javob ko'rsatilmagan yoki noto'g'ri")
            return

        questions.append({"question": q, "options": c["opts"], "correct": idx})

    for raw in text.splitlines():
        line = raw.strip()
        if not line:
            if cur is not None and cur["q"] and not cur["opts"]:
                cur["blank"] = True
            continue

        # ++++ : yangi savol boshlanadi, oldingisi tugaydi
        m = _SEP_Q_RE.match(line)
        if m:
            finish()
            line = m.group("rest").strip()
            if not line:
                continue

        # ==== : keyingi matn yangi variant
        m = _SEP_V_RE.match(line)
        if m:
            if cur is None:
                continue
            cur["delim"] = True
            cur["await"] = True
            line = m.group("rest").strip()
            if not line:
                continue

        # ****, ----, #### kabi bezaklar
        m = _DECOR_PREFIX_RE.match(line)
        if m:
            line = m.group("rest").strip()
            if not line:
                continue
        if _DECOR_ONLY_RE.match(line):
            continue

        m_ans = _ANSWER_RE.match(line)
        if m_ans and cur is not None and cur["opts"] and not cur["await"]:
            cur["answer"] = m_ans.group("ans")
            finish()
            continue

        # ==== dan keyingi qator: variant (harfli yoki harfsiz, # bilan belgilangan bo'lishi mumkin)
        if cur is not None and cur["await"]:
            cur["await"] = False
            body, marked = line, False
            mm = _MARK_RE.match(body)
            if mm:
                marked, body = True, body[mm.end():].strip()
            label = ""
            m_opt = _OPTION_STRICT_RE.match(body)
            if m_opt:
                label, body = _norm(m_opt.group("label")), m_opt.group("text")
            if not body:
                cur["await"] = True
                continue
            if marked and cur["marked"] is None:
                cur["marked"] = len(cur["opts"])
            cur["labels"].append(label)
            cur["opts"].append(body)
            continue

        # ==== usulida raqamlangan yangi savol: oldingisi tugaydi
        if cur is not None and cur["delim"] and cur["opts"] and _NUM_RE.match(line):
            finish()

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
            if cur["delim"]:
                cur["opts"][-1] += " " + line  # variant matni keyingi qatorga o'tgan
                continue
            finish()
        if cur is None:
            cur = new()
        if cur["q"] and not cur["opts"] and (cur["blank"] or _NUM_RE.match(line)):
            cur["q"] = []  # oldingi qatorlar sarlavha edi (institut nomi va h.k.)
        cur["blank"] = False
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
    "To'g'ri javobni \"Javob: B\" deb yoki to'g'ri variant oldiga *, + yoki # qo'yib ko'rsatasiz. "
    "Matnni xabar qilib, .txt yoki Word (.docx) fayl qilib yuborishingiz mumkin.\n\n"
    "Savollar orasida ++++, variantlar orasida ==== qo'yilgan va to'g'ri variant oldida # turgan "
    "matn ham o'qiladi (harflar shart emas):\n"
    "++++\n"
    "Savol matni?\n"
    "====\n"
    "Noto'g'ri variant\n"
    "====\n"
    "#To'g'ri variant\n\n"
    "Institut nomi kabi sarlavhalar va ====, ++++, ---- kabi belgilar savolga qo'shilmaydi. "
    "Sarlavhani savoldan bo'sh qator bilan ajrating yoki savollarni raqamlang.\n\n"
    "Bir martada 1000 tagacha savol yuborish mumkin (ko'p savollarni .txt yoki Word fayl qilib yuboring, "
    "chunki Telegram bitta xabar uzunligini cheklaydi). Savollar ko'p bo'lsa, ularni nechtadan alohida "
    "havolalarga bo'lishni tanlaysiz (masalan, 50, 100 yoki 200). So'ng har bir savol uchun vaqtni "
    "(15, 20 yoki 30 soniya) siz belgilaysiz va havola(lar) beriladi. Havola orqali kirganlardan "
    "vaqt so'ralmaydi."
)


# ---------------------------------------------------------------------------
# Word (.docx) fayldan matn olish
# ---------------------------------------------------------------------------

_W = "{http://schemas.openxmlformats.org/wordprocessingml/2006/main}"


def _read_zip_xml(zf, name: str):
    """Zip ichidagi XML faylni xavfsiz o'qiydi (juda katta yoki DOCTYPE/ENTITY bor bo'lsa rad etadi)."""
    try:
        info = zf.getinfo(name)
    except KeyError:
        return None
    if info.file_size > MAX_XML_BYTES:
        raise ValueError("Fayl juda katta")
    raw = zf.read(name)
    if b"<!DOCTYPE" in raw or b"<!ENTITY" in raw:
        raise ValueError("Noto'g'ri fayl")
    return ET.fromstring(raw)


def _letters(n: int) -> str:
    s = ""
    while n > 0:
        n, r = divmod(n - 1, 26)
        s = chr(97 + r) + s
    return s


def _roman(n: int) -> str:
    out = ""
    for val, sym in ((1000, "m"), (900, "cm"), (500, "d"), (400, "cd"), (100, "c"), (90, "xc"),
                     (50, "l"), (40, "xl"), (10, "x"), (9, "ix"), (5, "v"), (4, "iv"), (1, "i")):
        while n >= val:
            out += sym
            n -= val
    return out


def _fmt_counter(fmt: str, n: int):
    """Word raqamlash turini matnga aylantiradi; qo'llab-quvvatlanmasa (masalan, nuqta belgisi) None."""
    if fmt == "decimal":
        return str(n)
    if fmt == "lowerLetter":
        return _letters(n)
    if fmt == "upperLetter":
        return _letters(n).upper()
    if fmt == "lowerRoman":
        return _roman(n)
    if fmt == "upperRoman":
        return _roman(n).upper()
    return None


def _load_numbering(zf):
    """Word avtomatik raqamlash qoidalarini o'qiydi: (abstract, nums)."""
    abstract, nums = {}, {}
    root = _read_zip_xml(zf, "word/numbering.xml")
    if root is None:
        return abstract, nums
    for an in root.findall(_W + "abstractNum"):
        levels = {}
        for lvl in an.findall(_W + "lvl"):
            try:
                ilvl = int(lvl.get(_W + "ilvl", "0"))
            except ValueError:
                continue
            fmt, txt, st = lvl.find(_W + "numFmt"), lvl.find(_W + "lvlText"), lvl.find(_W + "start")
            start = st.get(_W + "val", "1") if st is not None else "1"
            levels[ilvl] = (
                fmt.get(_W + "val") if fmt is not None else "decimal",
                txt.get(_W + "val", "") if txt is not None else "",
                int(start) if start.isdigit() else 1,
            )
        abstract[an.get(_W + "abstractNumId")] = levels
    for num in root.findall(_W + "num"):
        a = num.find(_W + "abstractNumId")
        if a is not None:
            nums[num.get(_W + "numId")] = a.get(_W + "val")
    return abstract, nums


def _para_text(p) -> str:
    out = []
    for el in p.iter():
        if el.tag == _W + "t":
            out.append(el.text or "")
        elif el.tag == _W + "tab":
            out.append(" ")
        elif el.tag in (_W + "br", _W + "cr"):
            out.append("\n")  # qator uzilishi: variantlar bitta xatboshida bo'lsa ham ajraladi
    return "".join(out)


def docx_to_text(data: bytes) -> str:
    """Word (.docx) fayldan matnni oladi. Word o'zi qo'ygan raqam/harflar (1., a), b) ...) ham matnga qo'shiladi."""
    with zipfile.ZipFile(io.BytesIO(data)) as zf:
        doc = _read_zip_xml(zf, "word/document.xml")
        if doc is None:
            raise ValueError("Word fayli emas")
        abstract, nums = _load_numbering(zf)

    counters = {}  # numId -> {daraja: hisoblagich}
    lines = []
    for p in doc.iter(_W + "p"):  # jadval ichidagi xatboshilar ham tartib bilan olinadi
        text = _para_text(p)
        numpr = p.find(f"{_W}pPr/{_W}numPr")
        if numpr is not None:
            id_el, lvl_el = numpr.find(_W + "numId"), numpr.find(_W + "ilvl")
            num_id = id_el.get(_W + "val") if id_el is not None else None
            try:
                ilvl = int(lvl_el.get(_W + "val")) if lvl_el is not None else 0
            except (TypeError, ValueError):
                ilvl = 0
            if num_id and num_id != "0":
                levels = abstract.get(nums.get(num_id), {})
                cnt = counters.setdefault(num_id, {})
                fmt, lvl_text, start = levels.get(ilvl, ("decimal", "%" + str(ilvl + 1) + ".", 1))
                cnt[ilvl] = cnt.get(ilvl, start - 1) + 1
                for deeper in [k for k in cnt if k > ilvl]:
                    del cnt[deeper]  # yuqori daraja oshsa, pastki daraja qaytadan boshlanadi

                def sub(m, cnt=cnt, levels=levels):
                    lv = int(m.group(1)) - 1
                    lv_fmt, _, lv_start = levels.get(lv, ("decimal", "", 1))
                    return _fmt_counter(lv_fmt, cnt.get(lv, lv_start)) or ""

                label = re.sub(r"%(\d)", sub, lvl_text).strip() if _fmt_counter(fmt, 1) else ""
                if label and text.strip():
                    text = f"{label} {text}"
        lines.append(text)
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Quizni doimiy saqlash (GitHub Gist) va ulashish havolasi
# ---------------------------------------------------------------------------

_quiz_cache = {}  # quiz_id -> {"questions": [...], "seconds": int | None, "part": [...] | None}
_local_ids = set()  # faqat shu server xotirasidagi quizlar (havolasiz)
_pending = {}  # pid -> {"questions", "owner", "chunk"}: hali havolasi yaratilmagan quizlar


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


def _remember(quiz_id: str, questions: list, seconds, part=None) -> None:
    if len(_quiz_cache) >= 300:
        old = next(iter(_quiz_cache))
        _quiz_cache.pop(old)
        _local_ids.discard(old)
    _quiz_cache[quiz_id] = {"questions": questions, "seconds": seconds, "part": part}


def _quiz_content(questions: list, seconds, part=None) -> str:
    return json.dumps(
        {"v": 3, "seconds": seconds, "part": part, "questions": questions},
        ensure_ascii=False,
        separators=(",", ":"),
    )


def _save_quiz_sync(questions: list, seconds, part=None) -> str:
    content = _quiz_content(questions, seconds, part)
    if len(content.encode("utf-8")) > GIST_MAX_BYTES:
        raise ValueError("Quiz juda katta: uni kichikroq qismlarga bo'ling")
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
    _remember(quiz_id, questions, seconds, part)
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


def _validate_part(p):
    ok = (
        isinstance(p, list)
        and len(p) == 4
        and all(isinstance(x, int) and not isinstance(x, bool) and x > 0 for x in p)
        and p[0] <= p[1]
        and p[2] <= p[3]
    )
    return p if ok else None


def _validate_quiz(data):
    """Saqlangan quizni tekshiradi: {"questions", "seconds", "part"} yoki None."""
    questions = _validate_questions(data)
    if not questions:
        return None
    sec = data.get("seconds") if isinstance(data, dict) else None
    part = _validate_part(data.get("part")) if isinstance(data, dict) else None
    return {"questions": questions, "seconds": sec if sec in TIME_CHOICES else None, "part": part}


def _load_quiz_sync(quiz_id: str):
    if quiz_id in _quiz_cache:
        return _quiz_cache[quiz_id]
    resp = _gist_request("GET", f"/gists/{quiz_id}")
    f = resp["files"]["quiz.json"]
    if f.get("truncated"):
        raise ValueError("Quiz fayli juda katta")
    quiz = _validate_quiz(json.loads(f["content"]))
    if quiz:
        _remember(quiz_id, quiz["questions"], quiz["seconds"], quiz["part"])
    return quiz


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


def time_buttons(pid: str):
    """15 / 20 / 30 soniya tanlash tugmalari (bitta qator)."""
    return [
        InlineKeyboardButton(f"⏱ {s} soniya", callback_data=f"tm:{pid}:{s}")
        for s in TIME_CHOICES
    ]


def split_buttons(pid: str, n: int):
    """Quizni nechtadan bo'laklarga bo'lishni tanlash tugmalari."""
    sizes = [s for s in SPLIT_CHOICES if s < n]
    rows = [
        [InlineKeyboardButton(f"{s} tadan", callback_data=f"sp:{pid}:{s}") for s in sizes[i:i + 2]]
        for i in range(0, len(sizes), 2)
    ]
    rows.append([InlineKeyboardButton(f"Hammasi bitta havolada ({n})", callback_data=f"sp:{pid}:{n}")])
    return rows


def split_questions(questions: list, size: int):
    """Savollarni size tadan bo'laklarga bo'ladi: [(boshlanish raqami, tugash raqami, savollar), ...]."""
    return [
        (i + 1, min(i + size, len(questions)), questions[i:i + size])
        for i in range(0, len(questions), size)
    ]


def _share_url(link: str, text: str) -> str:
    return (
        "https://t.me/share/url?url="
        + urllib.parse.quote(link, safe="")
        + "&text="
        + urllib.parse.quote(text, safe="")
    )


def _new_pending(questions: list, owner: int) -> str:
    """Hali havolasi yaratilmagan quizni xotirada saqlaydi (bo'lish va vaqt tanlanguncha)."""
    if len(_pending) >= MAX_PENDING:
        _pending.pop(next(iter(_pending)))
    pid = uuid.uuid4().hex
    _pending[pid] = {"questions": questions, "owner": owner, "chunk": None}
    return pid


# ---------------------------------------------------------------------------
# Quizni chatga yuborish
# ---------------------------------------------------------------------------

async def _with_retry(fn, **kwargs):
    """Telegram tezlik cheklovi (RetryAfter) chiqsa, kutib, bir marta qayta urinadi."""
    try:
        return await fn(**kwargs)
    except RetryAfter as e:
        wait = e.retry_after
        wait = wait.total_seconds() if hasattr(wait, "total_seconds") else float(wait)
        await asyncio.sleep(wait + 1)
        return await fn(**kwargs)


async def _wait(event: asyncio.Event, seconds: float) -> None:
    """`seconds` kutadi, lekin to'xtatish signali kelsa darrov qaytadi."""
    try:
        await asyncio.wait_for(event.wait(), timeout=seconds)
    except asyncio.TimeoutError:
        pass


async def deliver_polls(
    bot,
    chat_id: int,
    questions: list,
    seconds: int,
    anonymous: bool = False,
    on_poll=None,
    start: int = 0,
    stop_event=None,
    answered=None,
    idle_limit: int = 0,
):
    """Savollarni `start` dan boshlab birin-ketin quiz so'rovnomasi qilib yuboradi.

    Har bir savol `seconds` soniya ochiq turadi (Telegram taymeri), shu vaqt o'tgach
    keyingisi yuboriladi. stop_event o'rnatilsa (qo'lda to'xtatish) yoki ketma-ket
    `idle_limit` ta savolga hech kim javob bermasa (answered(poll_id) False bo'lsa),
    yuborish to'xtaydi. Qaytaradi: (yuborilgan soni, xatolar, sabab, keyingi savol raqami);
    sabab: None (tugadi), "manual" yoki "idle".
    """
    sent, errors, idle = 0, [], 0
    reason, next_index = None, len(questions)
    stop_event = stop_event or asyncio.Event()
    for i in range(start, len(questions)):
        if stop_event.is_set():
            reason, next_index = "manual", i
            break
        q = questions[i]
        question = q["question"]
        poll_id = None
        try:
            if len(question) > MAX_QUESTION_LEN:
                # Quiz savoli 300 belgidan oshmasligi kerak: uzun savolni alohida xabar qilamiz.
                await _with_retry(bot.send_message, chat_id=chat_id, text=question[:4000])
                question = "Javobni tanlang:"
            message = await _with_retry(
                bot.send_poll,
                chat_id=chat_id,
                question=question,
                options=q["options"],
                type=Poll.QUIZ,
                correct_option_id=q["correct"],
                open_period=seconds,
                is_anonymous=anonymous,
            )
            poll = getattr(message, "poll", None)
            if poll is not None:
                poll_id = poll.id
                if on_poll is not None:
                    on_poll(poll.id, q["correct"], i, q)
            sent += 1
        except Exception:
            logger.exception("Quiz yuborishda xatolik")
            errors.append(f"{q['question'][:40]}: yuborib bo'lmadi")
        await _wait(stop_event, seconds)
        if stop_event.is_set():
            reason, next_index = "manual", i + 1
            break
        if answered is not None and poll_id is not None:
            idle = 0 if answered(poll_id) else idle + 1
            if idle_limit and idle >= idle_limit:
                reason, next_index = "idle", i + 1
                break
    if reason is not None and next_index >= len(questions):
        reason = None  # oxirgi savoldan keyin to'xtatishning ma'nosi yo'q: quiz tugadi
    return sent, errors, reason, next_index


def _ping_self(url: str) -> None:
    try:
        urllib.request.urlopen(url, timeout=10).read()
    except Exception:
        pass  # 404 ham bo'ladi: muhimi so'rov Render'ga yetib borishi


async def _keep_awake(stop: asyncio.Event) -> None:
    """Quiz davomida bepul Render xizmati uxlab qolmasligi uchun vaqti-vaqti bilan o'ziga so'rov yuboradi."""
    base = os.environ.get("WEBHOOK_URL") or os.environ.get("RENDER_EXTERNAL_URL")
    if not base:
        return
    while not stop.is_set():
        try:
            await asyncio.wait_for(stop.wait(), timeout=KEEP_AWAKE_SECONDS)
        except asyncio.TimeoutError:
            await asyncio.to_thread(_ping_self, base)


# ---------------------------------------------------------------------------
# Yaratuvchi: savollarni qabul qilish
# ---------------------------------------------------------------------------

TIME_PROMPT = (
    "Har bir savolga beriladigan vaqtni siz belgilaysiz. Havola orqali kirganlardan vaqt "
    "so'ralmaydi, quiz sizning vaqtingiz bilan ochiladi. Vaqtni tanlang:"
)
EXPIRED_TEXT = (
    "Savollar eskirgan (bot qayta ishga tushgan bo'lishi mumkin). "
    "Iltimos, savollarni qayta yuboring."
)


async def send_quiz(msg, bot, text: str, user_data=None) -> None:
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
    n = len(questions)

    pid = _new_pending(questions, msg.chat_id)
    if user_data is not None:
        user_data["split_pid"] = pid  # keyin yozilgan son (masalan, 75) shu quizga tegishli bo'ladi

    parts = [f"✅ {n} ta savol qabul qilindi."]
    if extra:
        parts.append(f"Bir martada {MAX_QUESTIONS} tagacha savol olinadi, {extra} tasi qoldi.")
    if errors:
        parts.append("O'tkazib yuborilganlar:\n" + "\n".join("- " + e for e in errors[:10]))
        if len(errors) > 10:
            parts.append(f"... va yana {len(errors) - 10} ta.")

    if n > min(SPLIT_CHOICES):
        parts.append(
            "Savollarni nechtadan qilib alohida havolalarga bo'lamiz? Masalan, bitta havolada "
            "100 ta savol yechmoqchi bo'lsangiz, \"100 tadan\" ni tanlang. Boshqa son kerak bo'lsa, "
            "shu sonni yozib yuboring (masalan, 75)."
        )
        markup = InlineKeyboardMarkup(split_buttons(pid, n))
    else:
        _pending[pid]["chunk"] = n
        parts.append(TIME_PROMPT)
        markup = InlineKeyboardMarkup([time_buttons(pid)])
    await msg.reply_text("\n\n".join(parts), reply_markup=markup)


async def apply_split(bot, chat_id: int, pid: str, size: int) -> None:
    """Quizni size tadan bo'laklarga bo'lishni belgilaydi va vaqt tanlashni so'raydi."""
    info = _pending.get(pid)
    if not info:
        await bot.send_message(chat_id=chat_id, text=EXPIRED_TEXT)
        return
    n = len(info["questions"])
    if size < min(MIN_CHUNK, n):
        await bot.send_message(
            chat_id=chat_id,
            text=(
                f"Bitta havolada kamida {MIN_CHUNK} ta savol bo'lishi kerak. "
                "Boshqa son yozing yoki tugmalardan birini tanlang."
            ),
        )
        return
    size = min(size, n)
    info["chunk"] = size
    k = -(-n // size)
    last = n - (k - 1) * size
    if k == 1:
        plan = "hammasi bitta havolada bo'ladi"
    elif last == size:
        plan = f"{k} ta havolaga bo'linadi, har birida {size} ta savol"
    else:
        plan = f"{k} ta havolaga bo'linadi: har birida {size} ta savol, oxirgisida {last} ta"
    await bot.send_message(
        chat_id=chat_id,
        text=f"📚 {n} ta savol: {plan}.\n\n" + TIME_PROMPT,
        reply_markup=InlineKeyboardMarkup([time_buttons(pid)]),
    )


async def choose_split(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Quiz yaratuvchisi nechtadan bo'lishni tanlaydi."""
    query = update.callback_query
    _, pid, size = query.data.split(":")
    chat = query.message.chat
    if chat.type != "private":
        await query.answer()
        return
    info = _pending.get(pid)
    if info and info["owner"] != chat.id:
        await query.answer("Buni faqat quiz yaratuvchisi tanlay oladi.", show_alert=True)
        return
    await query.answer()
    try:
        await query.edit_message_reply_markup(reply_markup=None)
    except Exception:
        pass
    await apply_split(context.bot, chat.id, pid, int(size))


def _create_parts(parts: list, seconds: int) -> list:
    """Har bir bo'lak uchun quiz yaratadi (GITHUB_TOKEN bo'lsa Gist'da, bo'lmasa faqat xotirada)."""
    out, k = [], len(parts)
    for i, (first, last, qs) in enumerate(parts, start=1):
        part = [i, k, first, last] if k > 1 else None
        quiz_id, shared = None, False
        if storage_enabled():
            try:
                quiz_id = _save_quiz_sync(qs, seconds, part)
                shared = True
            except Exception:
                logger.exception("Quiz havolasini yaratib bo'lmadi (%s-qism)", i)
        if quiz_id is None:
            quiz_id = uuid.uuid4().hex  # faqat shu server xotirasida: havolasiz ishlatish uchun
            _local_ids.add(quiz_id)
            _remember(quiz_id, qs, seconds, part)
        out.append({"id": quiz_id, "shared": shared, "index": i, "from": first, "to": last, "n": len(qs)})
    return out


async def send_links(bot, chat_id: int, created: list, total: int, seconds: int) -> None:
    k = len(created)
    head = f"⏱ Vaqt belgilandi: har bir savol {seconds} soniya ochiq turadi."
    tail = (
        "Havolani olgan odam botga kiradi, Start bosadi va quizni o'z chatida yoki guruhda ishlaydi. "
        "Undan vaqt so'ralmaydi, quiz siz belgilagan vaqt bilan ochiladi. Guruhda hamma natijani ko'radi."
    )

    if k == 1:
        c = created[0]
        text = f"{head} ({c['n']} ta savol)."
        rows = [[InlineKeyboardButton("▶️ Shu yerda boshlash", callback_data=f"run:{c['id']}")]]
        if c["shared"]:
            private_link, group_link = quiz_links(bot.username, c["id"])
            share_url = _share_url(private_link, f"Quiz: {c['n']} ta savol. Boshlash uchun havolani bosing.")
            text += f"\n\n🔗 Quiz havolasi:\n{private_link}\n\n{tail}"
            rows.append([InlineKeyboardButton("📨 Havolani yuborish", url=share_url)])
            rows.append([InlineKeyboardButton("👥 Guruhga qo'shish", url=group_link)])
        elif storage_enabled():
            text += "\n\nQuiz havolasini yaratib bo'lmadi, lekin quizni shu yerda boshlashingiz mumkin."
        await bot.send_message(chat_id=chat_id, text=text, reply_markup=InlineKeyboardMarkup(rows))
        return

    any_shared = any(c["shared"] for c in created)
    per_message = 8  # Telegram xabar uzunligi (4096 belgi) chegarasidan oshmaslik uchun
    for start in range(0, k, per_message):
        chunk = created[start:start + per_message]
        lines, rows = [], []
        for c in chunk:
            label = f"{c['index']}-qism ({c['from']}–{c['to']}-savollar, {c['n']} ta)"
            run_btn = InlineKeyboardButton(f"▶️ {c['index']}-qism", callback_data=f"run:{c['id']}")
            if c["shared"]:
                private_link, group_link = quiz_links(bot.username, c["id"])
                share_url = _share_url(
                    private_link, f"Quiz, {c['index']}-qism: {c['n']} ta savol. Boshlash uchun havolani bosing."
                )
                lines.append(f"{label}:\n{private_link}")
                rows.append([
                    run_btn,
                    InlineKeyboardButton("📨 Yuborish", url=share_url),
                    InlineKeyboardButton("👥 Guruhga", url=group_link),
                ])
            else:
                lines.append(f"{label}: havolasiz (faqat shu yerda ishlaydi)")
                rows.append([run_btn])
        text = "\n\n".join(lines)
        if start == 0:
            text = f"{head} {total} ta savol {k} ta havolaga bo'lindi:\n\n" + text
        if start + per_message >= k:
            if any_shared:
                text += "\n\n" + tail
            elif storage_enabled():
                text += "\n\nHavolalarni yaratib bo'lmadi, lekin qismlarni shu yerda boshlashingiz mumkin."
        await bot.send_message(chat_id=chat_id, text=text, reply_markup=InlineKeyboardMarkup(rows))


async def choose_time(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Quiz yaratuvchisi vaqtni tanlaydi: shundan keyin havola(lar) yaratiladi."""
    query = update.callback_query
    _, pid, sec = query.data.split(":")
    seconds = int(sec)
    chat = query.message.chat
    if seconds not in TIME_CHOICES or chat.type != "private":
        await query.answer()
        return
    info = _pending.get(pid)
    if info and info["owner"] != chat.id:
        await query.answer("Vaqtni faqat quiz yaratuvchisi belgilay oladi.", show_alert=True)
        return
    await query.answer()
    if not info:
        await context.bot.send_message(chat_id=chat.id, text=EXPIRED_TEXT)
        return

    _pending.pop(pid, None)  # tugma ikki marta bosilsa, havolalar ikki marta yaratilmasin
    if context.user_data.get("split_pid") == pid:
        context.user_data.pop("split_pid", None)
    try:
        await query.edit_message_reply_markup(reply_markup=None)  # tanlov bir marta
    except Exception:
        pass

    questions = info["questions"]
    parts = split_questions(questions, info["chunk"] or len(questions))
    if len(parts) > 1 and storage_enabled():
        await context.bot.send_message(
            chat_id=chat.id, text=f"⏳ {len(parts)} ta havola yaratilmoqda, biroz kuting..."
        )
    created = await asyncio.to_thread(_create_parts, parts, seconds)
    await send_links(context.bot, chat.id, created, len(questions), seconds)


# ---------------------------------------------------------------------------
# Bot buyruqlari, tugmalari va havola orqali ochish
# ---------------------------------------------------------------------------

HELP_TEXT = (
    "Men uchta ish qila olaman.\n\n"
    f"1) Rasmlarni PDF'ga aylantirish: menga rasmlarni yuboring ({MAX_IMAGES} tagacha), "
    f"keyin \"{BTN_PDF}\" tugmasini bosing. \"{BTN_CLEAR}\" yuborilgan rasmlarni o'chiradi. "
    "Rasmlarni fayl (hujjat) sifatida yuborsangiz, sifati yaxshiroq saqlanadi.\n\n"
    "2) Test savollaridan quiz yasash: savollarni matn qilib yuboring, so'ng har bir savol uchun "
    "vaqtni (15, 20 yoki 30 soniya) siz belgilaysiz, so'ng ulashish havolasi beriladi. "
    "Havolani olganlardan vaqt so'ralmaydi. "
    f"Format uchun \"{BTN_QUIZ}\" tugmasini bosing.\n\n"
    f"3) Slayd va referat: \"{BTN_GEN}\" tugmasini bosing, turini, hajmini va tilini tanlang, "
    "mavzuni yozing. Matnni sun'iy intellekt yozadi, men tayyor fayl (.pptx yoki .docx) beraman."
)


def _is_private(update: Update) -> bool:
    chat = update.effective_chat
    return chat is not None and chat.type == "private"


def _owner_id():
    raw = os.environ.get("OWNER_ID", "").strip()
    return int(raw) if raw.lstrip("-").isdigit() else None


async def notify_owner(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Botga Start bosgan odam haqida bot egasiga xabar yuboradi (har bir odam uchun bir marta)."""
    owner = _owner_id()
    user = update.effective_user
    if owner is None or user is None or user.is_bot or user.id == owner:
        return
    seen = context.application.bot_data.setdefault("seen", set())
    if user.id in seen:  # bot qayta ishga tushsa, ro'yxat bo'shaydi va xabar yana kelishi mumkin
        return
    seen.add(user.id)

    chat = update.effective_chat
    if chat is not None and chat.type != "private":
        where = f"guruh: {chat.title or chat.id}"
    else:
        where = "shaxsiy chat"
    via = " (quiz havolasi orqali)" if context.args and context.args[0].startswith(START_PREFIX) else ""
    nick = f"@{user.username}" if user.username else "yo'q"
    text = (
        f"👤 Botga yangi foydalanuvchi Start bosdi{via}\n"
        f"Ism: {user.full_name or '-'}\n"
        f"Nik: {nick}\n"
        f"ID: {user.id}\n"
        f"Joy: {where}"
    )
    try:
        await context.bot.send_message(chat_id=owner, text=text)
    except Exception as e:
        # Egasi botga o'zi Start bosmagan bo'lsa, Telegram xabar yuborishga ruxsat bermaydi
        logger.warning("Egasiga xabar yuborib bo'lmadi: %s", e)


async def myid(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Foydalanuvchining Telegram ID raqamini ko'rsatadi (OWNER_ID ni sozlash uchun)."""
    user = update.effective_user
    await update.message.reply_text(
        f"Sizning Telegram ID raqamingiz: {user.id}\n\n"
        "Bot egasi bo'lsangiz, shu raqamni Render'da OWNER_ID o'zgaruvchisiga yozing."
    )


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await notify_owner(update, context)
    if context.args and context.args[0].startswith(START_PREFIX):
        await open_quiz(update, context, context.args[0][len(START_PREFIX):])
        return
    await update.message.reply_text(
        "Salom! " + HELP_TEXT, reply_markup=KEYBOARD if _is_private(update) else None
    )


async def open_quiz(update: Update, context: ContextTypes.DEFAULT_TYPE, quiz_id: str) -> None:
    """Quiz havolasi orqali kirgan odamga quizni boshlash tugmasini ko'rsatadi.

    Vaqt quiz yaratuvchisi tomonidan belgilangan: qatnashuvchidan so'ralmaydi.
    """
    msg = update.message
    quiz = await load_quiz(quiz_id)
    if not quiz:
        await msg.reply_text(
            "Bu quiz topilmadi yoki eskirgan. Havolani yuborgan odamdan qayta so'rang."
        )
        return

    n = len(quiz["questions"])
    seconds = quiz["seconds"] or DEFAULT_SECONDS
    rows = [[InlineKeyboardButton("▶️ Boshlash", callback_data=f"run:{quiz_id}")]]
    part = quiz.get("part")
    label = f" ({part[0]}/{part[1]}-qism: {part[2]}–{part[3]}-savollar)" if part else ""
    info = f"📝 Quiz{label}: {n} ta savol, har biri {seconds} soniya (vaqtni quiz yaratuvchisi belgilagan)."
    if _is_private(update):
        _, group_link = quiz_links(context.bot.username, quiz_id)
        rows.append([InlineKeyboardButton("👥 Guruhda ishlatish", url=group_link)])
        text = (
            info + "\n\n\"Boshlash\" ni bosing, savollar shu chatga birin-ketin yuboriladi. "
            "Guruhda ishlatmoqchi bo'lsangiz, \"Guruhda ishlatish\" ni bosib guruhni tanlang."
        )
    else:
        text = (
            info + "\n\n\"Boshlash\" ni bosing, savollar shu guruhga birin-ketin yuboriladi. "
            "Natijalar ochiq: kim qaysi variantni tanlagani hammaga ko'rinadi. "
            "Oxirida natijalar o'rinlari bilan e'lon qilinadi."
        )
    await msg.reply_text(text, reply_markup=InlineKeyboardMarkup(rows))


def _track_poll(bot_data: dict, chat_id: int, poll_id: str, correct: int,
                q=None, idx: int = 0, run=None, seconds: int = 0) -> None:
    bot_data.setdefault("polls", {})[poll_id] = {
        "chat_id": chat_id,
        "correct": correct,
        "sent": time.monotonic(),
        "voters": set(),
        "q": q,
        "idx": idx,
        "run": run,
        "seconds": seconds,
    }


def _forget_chat(bot_data: dict, chat_id: int) -> None:
    """Chat uchun yig'ilgan kuzatuv ma'lumotlarini tozalaydi."""
    polls = bot_data.get("polls", {})
    for pid in [p for p, info in polls.items() if info["chat_id"] == chat_id]:
        polls.pop(pid, None)
    bot_data.get("scores", {}).pop(chat_id, None)


def _record_mistake(bot_data: dict, user_id: int, info: dict, wrong: bool) -> None:
    """Foydalanuvchining oxirgi quizdagi xato javob bergan savollarini eslab qoladi."""
    if info.get("q") is None or info.get("run") is None:
        return
    book = bot_data.setdefault("mistakes", {})
    rec = book.get(user_id)
    if rec is None or rec["run"] != info["run"]:
        # yangi quiz boshlandi: eski xatolar o'chadi (to'g'ri javob bergan bo'lsa ham)
        book.pop(user_id, None)
        rec = book[user_id] = {"run": info["run"], "seconds": info["seconds"], "items": {}}
        while len(book) > MAX_MISTAKE_USERS:
            book.pop(next(iter(book)))
    if wrong:
        rec["items"][info["idx"]] = info["q"]


async def poll_answer(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Guruhdagi quiz savollariga berilgan javoblarni hisoblab boradi."""
    ans = update.poll_answer
    bot_data = context.application.bot_data
    info = bot_data.get("polls", {}).get(ans.poll_id)
    user = getattr(ans, "user", None)
    if not info or user is None or user.id in info["voters"] or not ans.option_ids:
        return
    info["voters"].add(user.id)
    _record_mistake(bot_data, user.id, info, ans.option_ids[0] != info["correct"])
    board = bot_data.setdefault("scores", {}).setdefault(info["chat_id"], {})
    row = board.setdefault(user.id, {"name": user.full_name or "Ishtirokchi", "correct": 0, "time": 0.0})
    if ans.option_ids[0] == info["correct"]:
        row["correct"] += 1
        row["time"] += time.monotonic() - info["sent"]  # tenglikda tezroq javob bergan yuqorida


def build_results(board: dict, total: int) -> str:
    """O'rinlar va to'g'ri javoblar soni bilan natijalar matni."""
    if not board:
        return "🏆 Quiz natijalari\n\nHech kim javob bermadi."
    ranked = sorted(board.values(), key=lambda r: (-r["correct"], r["time"]))
    medals = ["🥇", "🥈", "🥉"]
    lines = []
    for i, r in enumerate(ranked[:MAX_RESULT_ROWS]):
        place = medals[i] if i < 3 else f"{i + 1}."
        lines.append(f"{place} {r['name'][:30]}: {r['correct']}/{total} ta to'g'ri")
    text = f"🏆 Quiz natijalari ({total} ta savol)\n\n" + "\n".join(lines)
    if len(ranked) > MAX_RESULT_ROWS:
        text += f"\n\n... va yana {len(ranked) - MAX_RESULT_ROWS} ta ishtirokchi."
    text += "\n\nBall teng bo'lsa, tezroq javob bergan yuqorida turadi."
    return text


def _stop_markup() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[InlineKeyboardButton("⏸ To'xtatish", callback_data="stp")]])


def _paused_markup(quiz_id: str, next_index: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton("▶️ Davom ettirish", callback_data=f"rs:{quiz_id}:{next_index}")],
            [InlineKeyboardButton("🔄 Boshidan boshlash", callback_data=f"run:{quiz_id}")],
        ]
    )


def _review_markup(label: str = "🔁 Xatolar ustida ishlash") -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[InlineKeyboardButton(label, callback_data="wr")]])


async def _play(context, chat_id: int, is_group: bool, starter: int, questions: list,
                seconds: int, start: int = 0, quiz_id=None, review: bool = False) -> None:
    """Savollarni chatga yuboradi: to'xtatish, avto-to'xtash va xatolarni eslab qolish bilan.

    review=True: foydalanuvchining oldingi xatolari shaxsiy chatda qayta yechiladi.
    """
    bot_data = context.application.bot_data
    running = bot_data.setdefault("running", set())
    running.add(chat_id)
    stop = asyncio.Event()
    bot_data.setdefault("sessions", {})[chat_id] = {"starter": starter, "stop": stop}
    stop_keep = asyncio.Event()
    keeper = asyncio.create_task(_keep_awake(stop_keep))
    intro = None
    finished = True
    runs = bot_data.setdefault("runs", {})
    try:
        if review or start == 0:
            run_id = uuid.uuid4().hex
            runs[chat_id] = run_id
        else:
            run_id = runs.setdefault(chat_id, uuid.uuid4().hex)
        if review:
            text = f"🔁 Xatolar ustida ishlash: {len(questions)} ta savol, har biri {seconds} soniya."
        elif start == 0:
            _forget_chat(bot_data, chat_id)  # eski ma'lumotlarni tozalab, yangidan boshlaymiz
            bot_data.setdefault("scores", {})[chat_id] = {}
            total_min = max(1, round(len(questions) * seconds / 60))
            text = (
                f"▶️ Quiz boshlandi: {len(questions)} ta savol, har biri {seconds} soniya "
                f"(jami taxminan {total_min} daqiqa)."
            )
        else:
            bot_data.setdefault("scores", {}).setdefault(chat_id, {})
            text = f"▶️ Quiz davom etmoqda: {start + 1}-savoldan, jami {len(questions)} ta savol."
        if is_group:
            text += (
                "\n👥 Natijalar ochiq: kim qaysi variantni tanlagani hammaga ko'rinadi. "
                "Oxirida natijalar o'rinlari bilan e'lon qilinadi."
            )
        text += (
            "\n⏸ To'xtatish tugmasini faqat quizni boshlagan odam bosa oladi. "
            f"Ketma-ket {IDLE_LIMIT} ta savolga hech kim javob bermasa, quiz o'zi to'xtaydi."
        )
        intro = await context.bot.send_message(
            chat_id=chat_id, text=text, reply_markup=_stop_markup()
        )
        on_poll = lambda pid, correct, idx, q: _track_poll(
            bot_data, chat_id, pid, correct, q, idx, run_id, seconds
        )
        answered = lambda pid: bool(bot_data.get("polls", {}).get(pid, {}).get("voters"))
        sent, errors, reason, next_index = await deliver_polls(
            context.bot, chat_id, questions, seconds, False, on_poll,
            start=start, stop_event=stop, answered=answered, idle_limit=IDLE_LIMIT,
        )
        if intro is not None:
            try:
                await context.bot.edit_message_reply_markup(
                    chat_id=chat_id, message_id=intro.message_id, reply_markup=None
                )
            except Exception:
                pass  # tugma olib tashlanmasa ham quizga halal bermaydi
        if reason is not None:
            finished = False
            if reason == "manual":
                head = "⏸ Quiz to'xtatildi."
            else:
                head = f"⏸ Ketma-ket {IDLE_LIMIT} ta savolga hech kim javob bermadi, quiz avtomatik to'xtatildi."
            if review:
                tail = "Xatolar saqlanib turadi: qaytadan boshlash uchun tugmani bosing."
                markup = _review_markup("🔁 Qaytadan boshlash")
            else:
                tail = (
                    "Ball saqlanib turadi. Davom ettirish yoki boshidan boshlash uchun tugmani bosing "
                    "(buni istagan odam bosa oladi)."
                )
                markup = _paused_markup(quiz_id, next_index)
            await context.bot.send_message(
                chat_id=chat_id,
                text=f"{head}\n{next_index}/{len(questions)} ta savol yuborildi. {tail}",
                reply_markup=markup,
            )
            return
        total_sent = start + sent
        if review:
            await asyncio.sleep(RESULT_GRACE)
            book = bot_data.get("mistakes", {})
            rec = book.get(starter)
            wrong = rec["items"] if rec and rec["run"] == run_id else {}
            if wrong:
                text = (
                    f"🏁 Xatolar ustida ishlash tugadi: {total_sent - len(wrong)}/{total_sent} ta to'g'ri. "
                    f"Hali {len(wrong)} ta savolda xato qoldi."
                )
                markup = _review_markup("🔁 Qolgan xatolarni yechish")
            else:
                book.pop(starter, None)
                text = "🎉 Barcha xatolar tuzatildi!"
                markup = None
            if errors:
                text += "\n\nYuborib bo'lmaganlar:\n" + "\n".join("- " + e for e in errors[:10])
            await context.bot.send_message(chat_id=chat_id, text=text, reply_markup=markup)
            return
        text = f"🏁 Quiz tugadi: {total_sent} ta savol yuborildi."
        if errors:
            text += "\n\nYuborib bo'lmaganlar:\n" + "\n".join("- " + e for e in errors[:10])
        if is_group:
            await context.bot.send_message(chat_id=chat_id, text=text)
            await asyncio.sleep(RESULT_GRACE)  # oxirgi javoblar yetib kelishi uchun
            board = bot_data.get("scores", {}).get(chat_id, {})
            text = build_results(board, total_sent)
        text += "\n\nXato qilgan bo'lsangiz, tugmani bosib shu savollarni qayta yeching."
        await context.bot.send_message(chat_id=chat_id, text=text, reply_markup=_review_markup())
    finally:
        if finished:
            _forget_chat(bot_data, chat_id)
        bot_data.get("sessions", {}).pop(chat_id, None)
        stop_keep.set()
        await keeper
        running.discard(chat_id)


async def _run_session(update: Update, context: ContextTypes.DEFAULT_TYPE, quiz_id: str, start: int) -> None:
    """Quizni `start`-savoldan boshlab shu chatga yuboradi."""
    query = update.callback_query
    chat = query.message.chat
    running = context.application.bot_data.setdefault("running", set())
    if chat.id in running:
        await query.answer("Quiz hozir ketmoqda, tugashini kuting.", show_alert=True)
        return
    await query.answer()
    quiz = await load_quiz(quiz_id)
    if not quiz:
        await context.bot.send_message(
            chat_id=chat.id,
            text="Bu quiz topilmadi yoki eskirgan. Havolani yuborgan odamdan qayta so'rang.",
        )
        return
    questions = quiz["questions"]
    if not 0 <= start < len(questions):
        start = 0
    await _play(
        context, chat.id, chat.type != "private", query.from_user.id, questions,
        quiz["seconds"] or DEFAULT_SECONDS, start, quiz_id,
    )


async def review_mistakes(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """\"Xatolar ustida ishlash\": foydalanuvchining xato javoblarini shaxsiy chatda qayta beradi."""
    query = update.callback_query
    user = query.from_user
    chat = query.message.chat
    bot_data = context.application.bot_data
    rec = bot_data.get("mistakes", {}).get(user.id)
    if not rec or not rec["items"]:
        await query.answer(
            "Sizda xato topilmadi: hammasi to'g'ri yoki ma'lumot eskirgan.", show_alert=True
        )
        return
    if user.id in bot_data.setdefault("running", set()):
        await query.answer("Siz hozir xatolar ustida ishlayapsiz, tugashini kuting.", show_alert=True)
        return
    if chat.type != "private":
        try:
            await context.bot.send_message(
                chat_id=user.id, text="🔁 Xatolaringiz shu yerga yuboriladi. Tayyor bo'ling..."
            )
        except Exception:
            await query.answer(
                "Avval botga shaxsiy chatda kirib Start bosing, so'ng tugmani qayta bosing.",
                show_alert=True,
            )
            return
    await query.answer("Xatolar shaxsiy chatga yuboriladi." if chat.type != "private" else None)
    items = [rec["items"][k] for k in sorted(rec["items"])]
    await _play(
        context, user.id, False, user.id, items, rec["seconds"] or DEFAULT_SECONDS, review=True
    )


async def run_quiz(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """\"Boshlash\" / \"Boshidan boshlash\" bosilganda quizni boshidan yuboradi."""
    quiz_id = update.callback_query.data.split(":", 1)[1]
    await _run_session(update, context, quiz_id, 0)


async def resume_quiz(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """\"Davom ettirish\" bosilganda to'xtagan joydan davom ettiradi."""
    query = update.callback_query
    _, quiz_id, idx = query.data.split(":")
    chat_id = query.message.chat.id
    if chat_id in context.application.bot_data.get("running", set()):
        await query.answer("Quiz hozir ketmoqda, tugashini kuting.", show_alert=True)
        return
    try:
        await query.edit_message_reply_markup(reply_markup=None)  # ikki marta bosilmasligi uchun
    except Exception:
        pass
    await _run_session(update, context, quiz_id, int(idx))


async def stop_quiz(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """\"To'xtatish\" tugmasi: faqat quizni boshlagan odam bosa oladi."""
    query = update.callback_query
    session = context.application.bot_data.get("sessions", {}).get(query.message.chat.id)
    if not session:
        await query.answer("Quiz hozir ketmayapti.", show_alert=True)
        return
    if query.from_user.id != session["starter"]:
        await query.answer("Quizni faqat uni boshlagan odam to'xtata oladi.", show_alert=True)
        return
    session["stop"].set()
    await query.answer("To'xtatilmoqda...")


async def help_cmd(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    context.user_data.pop("gen", None)  # boshqa tugma bosilsa, mavzu kutish bekor bo'ladi
    await update.message.reply_text(HELP_TEXT, reply_markup=KEYBOARD)


async def quiz_help(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    context.user_data.pop("gen", None)  # boshqa tugma bosilsa, mavzu kutish bekor bo'ladi
    await update.message.reply_text(QUIZ_FORMAT, reply_markup=KEYBOARD)


async def quiz_from_text(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    msg = update.message
    text = (msg.text or "").strip()
    if _gen_waiting_topic(context.user_data):
        if 3 <= len(text) <= 200 and "\n" not in text:
            await gen_generate(msg, context, text)
            return
        context.user_data.pop("gen", None)  # uzun/ko'p qatorli matn: bu mavzu emas, quiz savollari bo'lishi mumkin
    pid = context.user_data.get("split_pid")
    info = _pending.get(pid) if pid else None
    if info and info["owner"] == msg.chat_id and text.isdigit():
        # Quizni nechtadan bo'lish uchun son yozilgan (masalan, 75)
        await apply_split(context.bot, msg.chat_id, pid, int(text))
        return
    await send_quiz(msg, context.bot, msg.text or "", context.user_data)


async def quiz_from_file(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    msg = update.message
    doc = msg.document
    is_docx = (doc.file_name or "").lower().endswith(".docx")
    if doc.file_size and doc.file_size > (MAX_DOCX_BYTES if is_docx else MAX_TXT_BYTES):
        limit = "10 MB" if is_docx else "1 MB"
        await msg.reply_text(f"Fayl juda katta ({limit} gacha bo'lishi kerak).", reply_markup=KEYBOARD)
        return
    tg_file = await context.bot.get_file(doc.file_id)
    data = bytes(await tg_file.download_as_bytearray())
    if is_docx:
        try:
            text = await asyncio.to_thread(docx_to_text, data)
        except Exception:
            logger.exception("Word faylini o'qib bo'lmadi")
            await msg.reply_text(
                "Word faylini o'qib bo'lmadi. Fayl .docx formatida ekanini tekshiring.",
                reply_markup=KEYBOARD,
            )
            return
    else:
        try:
            text = data.decode("utf-8-sig")
        except UnicodeDecodeError:
            text = data.decode("cp1251", errors="replace")
    await send_quiz(msg, context.bot, text, context.user_data)


async def old_doc_format(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await update.message.reply_text(
        "Eski .doc formati qo'llab-quvvatlanmaydi. Faylni Word'da \"Saqlash\" (Save as) orqali "
        ".docx qilib saqlab, qayta yuboring.",
        reply_markup=KEYBOARD,
    )


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
    context.user_data.pop("gen", None)  # boshqa tugma bosilsa, mavzu kutish bekor bo'ladi
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
    context.user_data.pop("gen", None)  # boshqa tugma bosilsa, mavzu kutish bekor bo'ladi
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


# ---------------------------------------------------------------------------
# Slayd va referat (matnni sun'iy intellekt - Google Gemini yozadi)
# ---------------------------------------------------------------------------

GEMINI_BASE = "https://generativelanguage.googleapis.com/v1beta"
GEMINI_MODELS = ("gemini-flash-latest", "gemini-2.5-flash", "gemini-flash-lite-latest", "gemini-2.5-flash-lite")  # GEMINI_MODEL berilsa, faqat shu ishlatiladi
GEMINI_MIN_GAP = 6.5  # bepul limit (daqiqasiga ~10 so'rov) oshib ketmasligi uchun so'rovlar orasidagi pauza
GEN_DAILY_LIMIT = 5  # bitta foydalanuvchi bir kunda nechta slayd/referat olishi mumkin (egasi uchun cheklov yo'q)
GEN_SIZES = {"slide": (5, 10, 15), "essay": (5, 10, 15)}  # slaydlar soni / referat betlari soni
GEN_LANGS = {"uz": "Uzbek (Latin script)", "ru": "Russian", "en": "English"}
GEN_LANG_BUTTONS = {"uz": "🇺🇿 O'zbekcha", "ru": "🇷🇺 Ruscha", "en": "🇬🇧 Inglizcha"}
GEN_TOPIC_MINUTES = 15  # mavzu yozish uchun beriladigan vaqt
WORDS_PER_PAGE = 280

_gemini_gate = asyncio.Lock()
_gemini_last = [0.0]


class AIError(Exception):
    """Sun'iy intellekt javob bera olmadi (foydalanuvchiga ko'rsatiladigan matn bilan)."""

    def __init__(self, message: str, detail: str = ""):
        super().__init__(message)
        self.detail = detail  # texnik tafsilot: faqat bot egasiga ko'rsatiladi


def ai_key_status() -> str:
    """"ok", "missing" (kalit yo'q) yoki "bad" (kalit o'rniga boshqa narsa yozilgan)."""
    key = os.environ.get("GEMINI_API_KEY", "").strip()
    if not key:
        return "missing"
    return "ok" if re.fullmatch(r"[A-Za-z0-9_.\-]{20,200}", key) else "bad"


def ai_enabled() -> bool:
    return ai_key_status() == "ok"


def _gemini_sync(prompt: str, json_mode: bool) -> str:
    key = os.environ.get("GEMINI_API_KEY", "").strip()
    custom = os.environ.get("GEMINI_MODEL", "").strip()
    models = (custom,) if custom else GEMINI_MODELS
    config = {"temperature": 0.7, "maxOutputTokens": 16000}
    if json_mode:
        config["responseMimeType"] = "application/json"
    body = json.dumps(
        {"contents": [{"parts": [{"text": prompt}]}], "generationConfig": config}
    ).encode()
    details = []  # har bir model bo'yicha nima bo'lgani (egasi uchun)
    busy = False
    for model in models:
        url = f"{GEMINI_BASE}/models/{model}:generateContent"
        for attempt in range(2):
            req = urllib.request.Request(
                url, data=body, method="POST",
                headers={"Content-Type": "application/json", "x-goog-api-key": key},
            )
            try:
                with urllib.request.urlopen(req, timeout=120) as resp:
                    data = json.loads(resp.read().decode("utf-8"))
            except urllib.error.HTTPError as e:
                snippet = e.read()[:300].decode("utf-8", "replace").replace("\n", " ")
                details.append(f"{model}: {e.code} {snippet}")
                logger.warning("Gemini %s: HTTP %s %s", model, e.code, snippet)
                if e.code == 404:
                    break  # bu model yo'q: keyingisini sinaymiz
                if e.code == 429:
                    busy = True
                    break  # har bir modelning limiti alohida: darrov keyingisiga o'tamiz
                if e.code in (500, 502, 503, 504):
                    busy = True
                    if attempt == 0:
                        time.sleep(5)
                        continue
                    break
                if e.code in (400, 401, 403):
                    raise AIError(
                        "AI kaliti noto'g'ri yoki ruxsat yo'q. Bot egasiga xabar bering.",
                        "; ".join(details),
                    )
                break
            except (urllib.error.URLError, TimeoutError, OSError) as e:
                busy = True
                details.append(f"{model}: ulanish xatosi {type(e).__name__}")
                logger.warning("Gemini %s: ulanish xatosi %r", model, e)
                break
            try:
                cand = data["candidates"][0]
                text = "".join(p.get("text", "") for p in cand["content"]["parts"])
            except (KeyError, IndexError, TypeError):
                raise AIError(
                    "AI bu mavzuga javob bermadi. Mavzuni boshqacha yozib ko'ring.",
                    f"{model}: javobda matn yo'q: {str(data)[:200]}",
                )
            if not text.strip():
                raise AIError("AI bo'sh javob qaytardi. Qayta urinib ko'ring.", f"{model}: bo'sh matn")
            return text
    if busy:
        raise AIError(
            "AI xizmati band yoki bepul limit tugadi. Birozdan keyin urinib ko'ring.",
            "; ".join(details),
        )
    raise AIError("AI modeli topilmadi. Bot egasiga xabar bering.", "; ".join(details))


async def ask_ai(prompt: str, json_mode: bool = False) -> str:
    async with _gemini_gate:  # so'rovlar orasida pauza: bepul limitdan oshmaslik uchun
        wait = GEMINI_MIN_GAP - (time.monotonic() - _gemini_last[0])
        if wait > 0:
            await asyncio.sleep(wait)
        _gemini_last[0] = time.monotonic()
    return await asyncio.to_thread(_gemini_sync, prompt, json_mode)


def _parse_json_text(text: str):
    t = text.strip()
    t = re.sub(r"^```(?:json)?\s*|\s*```$", "", t)
    try:
        return json.loads(t)
    except ValueError:
        a, b = t.find("{"), t.rfind("}")
        if a != -1 and b > a:
            try:
                return json.loads(t[a : b + 1])
            except ValueError:
                pass
    raise AIError("AI javobini o'qib bo'lmadi. Qayta urinib ko'ring.")


def _clean(s, limit: int) -> str:
    s = re.sub(r"[*_#`]+", "", str(s or "")).strip()
    return re.sub(r"\s+", " ", s)[:limit]


async def ai_slides(topic: str, n: int, lang: str) -> dict:
    prompt = (
        f"You are an experienced teacher. Create a presentation on the topic: \"{topic}\".\n"
        f"Write it in {GEN_LANGS[lang]}. Exactly {n} slides.\n"
        "The first slide is an outline/plan, the last slide is the conclusion.\n"
        "Each slide has a short title (max 8 words) and 3-5 bullets (each max 18 words).\n"
        "Do not invent statistics, quotes or sources; stay with well-established facts.\n"
        'Return only JSON: {"title": "...", "slides": [{"title": "...", "bullets": ["..."]}]}'
    )
    data = _parse_json_text(await ask_ai(prompt, json_mode=True))
    slides = []
    for s in data.get("slides", []) if isinstance(data, dict) else []:
        if not isinstance(s, dict):
            continue
        bullets = [_clean(b, 220) for b in (s.get("bullets") or []) if _clean(b, 220)][:6]
        title = _clean(s.get("title"), 100)
        if title and bullets:
            slides.append({"title": title, "bullets": bullets})
    if len(slides) < 3:
        raise AIError("AI yetarli slayd yozmadi. Qayta urinib ko'ring.")
    return {"title": _clean(data.get("title"), 150) or topic, "slides": slides[: n + 2]}


def _section_plan(pages: int) -> list:
    main = {5: 2, 10: 4, 15: 6}.get(pages, max(2, pages // 3))
    return main + 2  # kirish + asosiy qismlar + xulosa


async def ai_essay(topic: str, pages: int, lang: str, progress=None) -> dict:
    total = _section_plan(pages)
    prompt = (
        f"Make an outline for an academic essay (referat) on the topic: \"{topic}\".\n"
        f"Language: {GEN_LANGS[lang]}. Exactly {total} section headings: the first is the introduction, "
        "the last is the conclusion, the others are main parts with specific, distinct headings.\n"
        'Return only JSON: {"title": "...", "sections": ["heading 1", "heading 2"]}'
    )
    data = _parse_json_text(await ask_ai(prompt, json_mode=True))
    heads = [_clean(h, 120) for h in (data.get("sections") or []) if _clean(h, 120)] if isinstance(data, dict) else []
    if len(heads) < 3:
        raise AIError("AI referat rejasini tuzmadi. Qayta urinib ko'ring.")
    heads = heads[: total + 1]
    weights = [0.6 if i in (0, len(heads) - 1) else 1.0 for i in range(len(heads))]
    words_total = pages * WORDS_PER_PAGE
    sections = []
    for i, head in enumerate(heads):
        if progress:
            await progress(i, len(heads))
        words = max(120, int(words_total * weights[i] / sum(weights)))
        prompt = (
            f"Write one section of an academic essay (referat) on the topic \"{topic}\".\n"
            f"Outline of the whole essay: {'; '.join(heads)}.\n"
            f"Write ONLY the section \"{head}\", about {words} words, in {GEN_LANGS[lang]}.\n"
            "Plain paragraphs separated by blank lines. No headings, no markdown, no lists, "
            "no invented statistics, quotes or references."
        )
        text = await ask_ai(prompt)
        paras = [_clean(p, 3000) for p in re.split(r"\n\s*\n", text) if _clean(p, 3000)]
        if not paras:
            raise AIError("AI bo'sh bo'lim yozdi. Qayta urinib ko'ring.")
        sections.append({"heading": head, "paragraphs": paras})
    return {"title": _clean(data.get("title"), 150) or topic, "sections": sections}


def build_pptx(deck: dict) -> bytes:
    from pptx import Presentation
    from pptx.dml.color import RGBColor
    from pptx.enum.text import PP_ALIGN, MSO_ANCHOR
    from pptx.util import Inches, Pt

    navy, accent, ink = RGBColor(0x1F, 0x3A, 0x5F), RGBColor(0xE0, 0x8E, 0x2B), RGBColor(0x26, 0x32, 0x38)
    prs = Presentation()
    prs.slide_width, prs.slide_height = Inches(13.333), Inches(7.5)
    blank = prs.slide_layouts[6]

    def box(slide, x, y, w, h, fill=None):
        shape = slide.shapes.add_shape(1, Inches(x), Inches(y), Inches(w), Inches(h))
        shape.line.fill.background()
        if fill is not None:
            shape.fill.solid()
            shape.fill.fore_color.rgb = fill
        return shape

    def text(slide, x, y, w, h, value, size, color, bold=False, align=PP_ALIGN.LEFT, anchor=MSO_ANCHOR.TOP):
        tb = slide.shapes.add_textbox(Inches(x), Inches(y), Inches(w), Inches(h))
        tf = tb.text_frame
        tf.word_wrap = True
        tf.vertical_anchor = anchor
        p = tf.paragraphs[0]
        p.alignment = align
        r = p.add_run()
        r.text = value
        r.font.size, r.font.bold, r.font.name = Pt(size), bold, "Calibri"
        r.font.color.rgb = color
        return tf

    cover = prs.slides.add_slide(blank)
    box(cover, 0, 0, 13.333, 7.5, navy)
    box(cover, 0.9, 3.05, 1.6, 0.09, accent)
    text(cover, 0.9, 1.0, 11.5, 2.0, deck["title"], 44 if len(deck["title"]) < 70 else 34, RGBColor(255, 255, 255), True, anchor=MSO_ANCHOR.BOTTOM)

    for number, s in enumerate(deck["slides"], start=1):
        sl = prs.slides.add_slide(blank)
        box(sl, 0, 0, 0.35, 7.5, navy)
        box(sl, 0.9, 1.45, 1.0, 0.07, accent)
        text(sl, 0.9, 0.45, 11.6, 1.0, s["title"], 34 if len(s["title"]) < 50 else 28, navy, True, anchor=MSO_ANCHOR.MIDDLE)
        total_chars = sum(len(b) for b in s["bullets"])
        size = 26 if total_chars < 260 else 22 if total_chars < 420 else 18
        tb = sl.shapes.add_textbox(Inches(0.9), Inches(1.8), Inches(11.5), Inches(5.0))
        tf = tb.text_frame
        tf.word_wrap = True
        for i, b in enumerate(s["bullets"]):
            p = tf.paragraphs[0] if i == 0 else tf.add_paragraph()
            p.space_after = Pt(14)
            r = p.add_run()
            r.text = "•  " + b
            r.font.size, r.font.name = Pt(size), "Calibri"
            r.font.color.rgb = ink
        text(sl, 12.0, 6.95, 1.0, 0.4, str(number), 14, RGBColor(0x78, 0x90, 0x9C), align=PP_ALIGN.RIGHT)

    out = io.BytesIO()
    prs.save(out)
    return out.getvalue()


def build_docx(essay: dict) -> bytes:
    from docx import Document
    from docx.enum.text import WD_ALIGN_PARAGRAPH, WD_BREAK
    from docx.oxml import OxmlElement
    from docx.oxml.ns import qn
    from docx.shared import Cm, Pt

    doc = Document()
    sec = doc.sections[0]
    sec.left_margin, sec.right_margin = Cm(3), Cm(1.5)
    sec.top_margin = sec.bottom_margin = Cm(2)

    def font(run, size=14, bold=False):
        run.font.name = "Times New Roman"
        run._element.rPr.rFonts.set(qn("w:eastAsia"), "Times New Roman")
        run.font.size, run.font.bold = Pt(size), bold

    def para(value, size=14, bold=False, align=WD_ALIGN_PARAGRAPH.JUSTIFY, indent=True, after=0):
        p = doc.add_paragraph()
        p.alignment = align
        p.paragraph_format.line_spacing = 1.5
        p.paragraph_format.space_after = Pt(after)
        if indent:
            p.paragraph_format.first_line_indent = Cm(1.25)
        font(p.add_run(value), size, bold)
        return p

    # Sarlavha varag'i
    for _ in range(7):
        doc.add_paragraph()
    para("REFERAT", 20, True, WD_ALIGN_PARAGRAPH.CENTER, False, 18)
    para("Mavzu:", 14, False, WD_ALIGN_PARAGRAPH.CENTER, False)
    para(essay["title"], 18, True, WD_ALIGN_PARAGRAPH.CENTER, False)
    doc.add_paragraph().add_run().add_break(WD_BREAK.PAGE)

    # Reja
    para("REJA", 16, True, WD_ALIGN_PARAGRAPH.CENTER, False, 6)
    for i, s in enumerate(essay["sections"], start=1):
        para(f"{i}. {s['heading']}", 14, False, WD_ALIGN_PARAGRAPH.LEFT, False)
    doc.add_paragraph().add_run().add_break(WD_BREAK.PAGE)

    for i, s in enumerate(essay["sections"], start=1):
        para(f"{i}. {s['heading']}", 16, True, WD_ALIGN_PARAGRAPH.CENTER, False, 6)
        for t in s["paragraphs"]:
            para(t)

    # Sahifa raqami (pastda, o'rtada)
    fp = sec.footer.paragraphs[0]
    fp.alignment = WD_ALIGN_PARAGRAPH.CENTER
    run = fp.add_run()
    font(run, 12)
    for kind, txt in (("begin", None), (None, "PAGE"), ("end", None)):
        if kind:
            el = OxmlElement("w:fldChar")
            el.set(qn("w:fldCharType"), kind)
        else:
            el = OxmlElement("w:instrText")
            el.set(qn("xml:space"), "preserve")
            el.text = txt
        run._r.append(el)

    out = io.BytesIO()
    doc.save(out)
    return out.getvalue()


def _today_key() -> str:
    from datetime import datetime, timedelta, timezone

    return datetime.now(timezone(timedelta(hours=5))).strftime("%Y-%m-%d")  # O'zbekiston vaqti


def _gen_used(bot_data: dict, user_id: int) -> int:
    day, count = bot_data.setdefault("gen_usage", {}).get(user_id, (None, 0))
    return count if day == _today_key() else 0


def _gen_filename(topic: str, ext: str) -> str:
    slug = re.sub(r"[^\w]+", "_", topic, flags=re.UNICODE).strip("_")[:40] or "fayl"
    return f"{slug}.{ext}"


def _gen_kind_markup() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        [
            [InlineKeyboardButton("📊 Slayd (.pptx)", callback_data="gn:k:slide")],
            [InlineKeyboardButton("📝 Referat (.docx)", callback_data="gn:k:essay")],
        ]
    )


async def gen_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    msg = update.message
    context.user_data.pop("gen", None)
    status = ai_key_status()
    if status != "ok":
        if status == "bad":
            text = (
                "GEMINI_API_KEY noto'g'ri yozilgan: qiymatida kalit o'rniga boshqa matn (masalan, kod) turibdi. "
                "Render'da uni o'chirib, aistudio.google.com dagi kalitning o'zini (AIza... yoki AQ.... ko'rinishida, bitta qatorda) qo'ying."
            )
        else:
            text = "Bu funksiya hali yoqilmagan: bot egasi Render'da GEMINI_API_KEY ni qo'shishi kerak."
        await msg.reply_text(text, reply_markup=KEYBOARD)
        return
    await msg.reply_text(
        "Nimani tayyorlay? Matnni sun'iy intellekt yozadi.", reply_markup=_gen_kind_markup()
    )


async def gen_choice(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Slayd/referat tanlovlari: tur -> hajm -> til, keyin mavzu so'raladi."""
    query = update.callback_query
    _, step, value = query.data.split(":")
    state = context.user_data.get("gen")
    if step == "k":
        if value not in GEN_SIZES:
            await query.answer()
            return
        state = context.user_data["gen"] = {"kind": value}
        label = "slayd soni" if value == "slide" else "referat hajmi (taxminan bet)"
        rows = [[InlineKeyboardButton(str(n), callback_data=f"gn:n:{n}") for n in GEN_SIZES[value]]]
        await query.answer()
        await query.edit_message_text(f"Tanlang: {label}", reply_markup=InlineKeyboardMarkup(rows))
        return
    if not state:
        await query.answer("Bu tanlov eskirgan. \"" + BTN_GEN + "\" ni qayta bosing.", show_alert=True)
        return
    if step == "n" and value.isdigit() and int(value) in GEN_SIZES[state["kind"]]:
        state["n"] = int(value)
        rows = [[InlineKeyboardButton(label, callback_data=f"gn:l:{code}")] for code, label in GEN_LANG_BUTTONS.items()]
        await query.answer()
        await query.edit_message_text("Qaysi tilda yozilsin?", reply_markup=InlineKeyboardMarkup(rows))
    elif step == "l" and value in GEN_LANGS and "n" in state:
        state["lang"] = value
        state["until"] = time.monotonic() + GEN_TOPIC_MINUTES * 60
        state["stage"] = "topic"
        await query.answer()
        await query.edit_message_text(
            "Endi mavzuni bitta xabar qilib yozing. Masalan: \"Amir Temur davlati\" yoki \"Fotosintez jarayoni\"."
        )
    else:
        await query.answer()


async def gen_generate(msg, context: ContextTypes.DEFAULT_TYPE, topic: str) -> None:
    state = context.user_data.pop("gen")
    bot_data = context.application.bot_data
    user_id = msg.chat_id
    busy = bot_data.setdefault("gen_running", set())
    owner = _owner_id()
    if user_id != owner and _gen_used(bot_data, user_id) >= GEN_DAILY_LIMIT:
        await msg.reply_text(
            f"Bugungi limit tugadi: kuniga {GEN_DAILY_LIMIT} tadan tayyorlash mumkin. Ertaga qayta urinib ko'ring.",
            reply_markup=KEYBOARD,
        )
        return
    if user_id in busy:
        await msg.reply_text("Oldingi so'rovingiz hali tayyorlanmoqda, kuting.", reply_markup=KEYBOARD)
        return
    busy.add(user_id)
    kind, n, lang = state["kind"], state["n"], state["lang"]
    try:
        note = await msg.reply_text(
            "⏳ Tayyorlanmoqda, taxminan 1-3 daqiqa kuting..." if kind == "essay" else "⏳ Tayyorlanmoqda, bir daqiqa kuting...",
            reply_markup=KEYBOARD,
        )

        async def progress(i, total):
            try:
                await note.edit_text(f"⏳ Referat yozilmoqda: {i + 1}/{total}-bo'lim...")
            except Exception:
                pass  # xabar tahrirlanmasa ham ish davom etadi

        if kind == "slide":
            data = await ai_slides(topic, n, lang)
            blob = await asyncio.to_thread(build_pptx, data)
            filename, caption = _gen_filename(topic, "pptx"), f"📊 Slayd tayyor: {len(data['slides'])} ta slayd."
        else:
            data = await ai_essay(topic, n, lang, progress)
            blob = await asyncio.to_thread(build_docx, data)
            filename, caption = _gen_filename(topic, "docx"), "📝 Referat tayyor."
        caption += "\n⚠️ Matnni sun'iy intellekt yozdi: faktlar va sanalarni tekshirib, o'zingizcha tahrir qiling."
        await msg.reply_document(io.BytesIO(blob), filename=filename, caption=caption, reply_markup=KEYBOARD)
        bot_data["gen_usage"][user_id] = (_today_key(), _gen_used(bot_data, user_id) + 1)
    except AIError as e:
        text = str(e)
        if user_id == owner and e.detail:
            text += "\n\n[Faqat egasiga ko'rinadi]\n" + e.detail[:800]
        await msg.reply_text(text, reply_markup=KEYBOARD)
    except ImportError:
        logger.exception("python-pptx / python-docx o'rnatilmagan")
        await msg.reply_text(
            "Fayl yaratish kutubxonasi o'rnatilmagan. Bot egasi requirements.txt ga python-pptx va python-docx qo'shishi kerak.",
            reply_markup=KEYBOARD,
        )
    except Exception:
        logger.exception("Slayd/referat yaratishda xatolik")
        await msg.reply_text("Xatolik yuz berdi. Birozdan keyin qayta urinib ko'ring.", reply_markup=KEYBOARD)
    finally:
        busy.discard(user_id)


def _gen_waiting_topic(user_data: dict) -> bool:
    state = user_data.get("gen")
    if not state or state.get("stage") != "topic":
        return False
    if time.monotonic() > state.get("until", 0):
        user_data.pop("gen", None)
        return False
    return True


def main() -> None:
    token = os.environ["BOT_TOKEN"]
    # Uzoq PDF yoki ko'p quiz yuborilayotganda boshqa foydalanuvchilar kutib qolmasligi uchun
    app = Application.builder().token(token).concurrent_updates(True).build()

    # /start hamma joyda ishlaydi (guruhda ham: quiz havolasi shu orqali ochiladi)
    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("myid", myid))
    app.add_handler(CallbackQueryHandler(choose_split, pattern=r"^sp:[0-9a-f]{20,40}:\d{1,4}$"))
    app.add_handler(CallbackQueryHandler(choose_time, pattern=r"^tm:[0-9a-f]{20,40}:(15|20|30)$"))
    app.add_handler(CallbackQueryHandler(run_quiz, pattern=r"^run:[0-9a-f]{20,40}$"))
    app.add_handler(CallbackQueryHandler(resume_quiz, pattern=r"^rs:[0-9a-f]{20,40}:\d{1,4}$"))
    app.add_handler(CallbackQueryHandler(stop_quiz, pattern=r"^stp$"))
    app.add_handler(CallbackQueryHandler(review_mistakes, pattern=r"^wr$"))
    app.add_handler(CallbackQueryHandler(gen_choice, pattern=r"^gn:[knl]:[a-z0-9]{1,8}$"))
    app.add_handler(PollAnswerHandler(poll_answer))  # guruhdagi javoblarni hisoblash uchun

    # Qolgan hamma narsa faqat shaxsiy chatda: guruhdagi oddiy suhbatga bot aralashmaydi
    private = filters.ChatType.PRIVATE

    # Tugmalar (ular umumiy matn qabul qiluvchidan oldin turishi kerak)
    app.add_handler(MessageHandler(private & filters.Text([BTN_PDF]), make_pdf))
    app.add_handler(MessageHandler(private & filters.Text([BTN_QUIZ]), quiz_help))
    app.add_handler(MessageHandler(private & filters.Text([BTN_GEN]), gen_start))
    app.add_handler(MessageHandler(private & filters.Text([BTN_CLEAR]), clear))
    app.add_handler(MessageHandler(private & filters.Text([BTN_HELP]), help_cmd))

    app.add_handler(
        MessageHandler(private & (filters.PHOTO | filters.Document.IMAGE), add_image)
    )
    app.add_handler(
        MessageHandler(
            private
            & (filters.Document.FileExtension("txt") | filters.Document.FileExtension("docx")),
            quiz_from_file,
        )
    )
    app.add_handler(MessageHandler(private & filters.Document.FileExtension("doc"), old_doc_format))
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
            allowed_updates=Update.ALL_TYPES,  # poll_answer ham kelishi uchun
        )
    else:
        logger.info("Polling rejimi (mahalliy sinov)")
        app.run_polling(allowed_updates=Update.ALL_TYPES)


if __name__ == "__main__":
    main()
