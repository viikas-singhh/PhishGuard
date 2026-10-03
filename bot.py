import asyncio, base64, ipaddress, os, re, ssl, time, uuid
from dataclasses import dataclass
from datetime import datetime, timezone
from html import escape
from urllib.parse import urlparse

import aiohttp
import tldextract
from aiogram import Bot, Dispatcher, F
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.filters import CommandStart
from aiogram.types import (Message, InlineQuery, InlineQueryResultArticle,
                           InputTextMessageContent)
from dotenv import load_dotenv
from rapidfuzz.distance import Levenshtein

load_dotenv()
TELEGRAM_TOKEN = os.getenv("TELEGRAM_TOKEN", "")
VT_API_KEY = os.getenv("VT_API_KEY", "")
GSB_API_KEY = os.getenv("GSB_API_KEY", "")

if not TELEGRAM_TOKEN:
    raise SystemExit("❌ No TELEGRAM_TOKEN found in .env")

HEADERS = {"User-Agent": "Mozilla/5.0 (X11; Linux x86_64) PhishGuard/0.1"}
CONTENT_HEADERS = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                                 "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
                   "Accept-Language": "en-US,en;q=0.9"}

# ---------------- knowledge base ----------------
BRANDS = [
    # fintech & tech
    "paypal", "apple", "icloud", "microsoft", "office365", "outlook",
    "google", "gmail", "amazon", "netflix", "whatsapp", "instagram",
    "facebook", "linkedin", "spotify", "walmart", "ebay", "steam", "roblox",
    "revolut", "wellsfargo", "chase", "hsbc", "santander", "dhl", "fedex", "ups",
    # gambling — top cloned brands
    "stake", "bet365", "1xbet", "parimatch", "mostbet", "dafabet", "rajabets",
    "4rabet", "melbet", "22bet", "betway", "betfair", "unibet", "draftkings",
    "fanduel", "pokerstars", "williamhill", "leovegas", "dream11",
    # crypto
    "binance", "coinbase", "metamask", "bybit", "kucoin", "okx", "kraken",
    "bitfinex", "bitget", "bitmex", "ledger", "trezor", "trustwallet",
    # india fintech + payments
    "paytm", "phonepe", "razorpay", "wazirx", "coindcx", "zebpay",
    "cashapp", "venmo", "zelle",
]

# domain-slug scam vocabulary (hyphen-separated tokens only)
GAMBLING_KW = {"casino", "casinos", "slots", "poker", "roulette", "blackjack",
               "bingo", "jackpot", "spins", "betting", "bet", "wager", "pokies",
               "rummy", "satta", "matka", "teenpatti", "lottery", "lotto", "keno"}
CRYPTO_KW = {"wallet", "airdrop", "mining", "token", "presale", "faucet", "swap"}
TRUST_KW = {"login", "signin", "verify", "verification", "account", "secure",
            "security", "official", "update", "alert", "suspend", "unlock",
            "recovery", "refund", "helpdesk", "billing", "invoice", "otp", "kyc"}
FREE_KW = {"free", "earn", "cash", "bonus", "promo", "hack", "mod", "cheat",
           "generator", "crack", "premium", "income", "money", "profit"}
SCAM_KW = GAMBLING_KW | CRYPTO_KW | TRUST_KW | FREE_KW

# page-content scam vocabulary (substring match on stripped page text)
CONTENT_GAMBLING = ["casino", "online slots", "slot games", "jackpot", "welcome bonus",
                    "sign up bonus", "free spins", "deposit bonus", "sports betting",
                    "pokies", "satta", "teen patti", "rummy", "andar bahar",
                    "wagering", "bet now", "place your bet"]
CONTENT_BAIT = ["account suspended", "account locked", "verify your account",
                "confirm your identity", "unusual activity", "urgent action",
                "security alert", "identity verification", "update your payment",
                "billing information"]
CONTENT_DRAINER = ["seed phrase", "recovery phrase", "private key", "connect wallet",
                   "sync wallet", "validate wallet", "12 words", "24 words", "mnemonic"]
CONTENT_FREEBAIT = ["double your", "claim your", "free gift", "giveaway", "send crypto",
                    "send btc", "send eth", "send usdt", "guaranteed profit"]

# TLD reputation tiers (abuse-rate based; review quarterly vs Spamhaus stats)
INSTITUTIONAL = {"gov", "mil", "edu", "int",
                 "gov.uk", "gov.in", "gov.au", "gov.sg",
                 "ac.uk", "edu.in", "edu.au"}
MAINSTREAM = {"com", "org", "net", "in", "uk", "us", "de", "fr", "it", "es", "nl",
              "se", "no", "fi", "dk", "ch", "at", "be", "pl", "pt", "ie", "cz",
              "gr", "ro", "jp", "kr", "au", "ca", "nz", "br", "mx", "ar", "cl",
              "za", "sg", "ae", "sa", "il", "my", "th", "ph", "id",
              "co.in", "co.uk", "org.uk", "com.au", "com.br", "co.jp",
              "tech", "io", "ai", "app", "dev", "me", "tv", "gg", "so", "co"}
HIGH_ABUSE = {"tk", "ml", "ga", "cf", "gq", "buzz", "cam", "quest", "sbs",
              "monster", "cyou", "zip", "mov", "work", "loan", "click",
              "racing", "download", "review", "country"}
ELEVATED = {"xyz", "top", "icu", "live", "link", "rest", "fit", "shop", "free",
            "cc", "pw", "vip", "club", "fun", "online", "site", "website",
            "space", "host", "store", "cfd", "lat", "kz", "su", "ru"}

SHORTENERS = {"bit.ly", "tinyurl.com", "t.co", "goo.gl", "is.gd",
              "cutt.ly", "rb.gy", "shorturl.at", "tiny.cc", "ow.ly", "buff.ly"}
URL_RE = re.compile(
    r"(?:https?://|www\.)[^\s]+|(?:[a-z0-9-]+\.)+[a-z]{2,}(?:/[^\s]*)?", re.I)

@dataclass
class Finding:
    text: str
    points: int = 0   # >0 = problem, 0 = neutral, <0 = good
    icon: str = "●"

# ---------------- RDAP (domain age) with registry fallback ----------------
_BOOTSTRAP: dict[str, str] = {}
_BOOTSTRAP_TIME = 0.0

async def _load_bootstrap(session) -> dict[str, str]:
    global _BOOTSTRAP_TIME
    if _BOOTSTRAP and time.time() - _BOOTSTRAP_TIME < 86400:
        return _BOOTSTRAP
    try:
        async with session.get("https://data.iana.org/rdap/dns.json",
                               timeout=aiohttp.ClientTimeout(total=10)) as r:
            data = await r.json(content_type=None)
        for tlds, servers in data["services"]:
            for t in tlds:
                _BOOTSTRAP[t] = servers[0]
        _BOOTSTRAP_TIME = time.time()
        print(f"[rdap] bootstrap loaded: {len(_BOOTSTRAP)} TLDs")
    except Exception as e:
        print(f"[rdap] bootstrap load failed: {e!r}")
    return _BOOTSTRAP

async def fetch_rdap(registered_domain: str, session) -> dict | None:
    labels = registered_domain.split(".")
    candidates = [f"https://rdap.org/domain/{registered_domain}"]
    boot = await _load_bootstrap(session)
    base = boot.get(".".join(labels[-2:])) or boot.get(labels[-1])
    if base:
        candidates.append(base.rstrip("/") + "/domain/" + registered_domain)
    for u in candidates:
        try:
            async with session.get(u, timeout=aiohttp.ClientTimeout(total=12)) as r:
                if r.status == 200:
                    return await r.json(content_type=None)
                print(f"[rdap] {u} -> HTTP {r.status}")
        except Exception as e:
            print(f"[rdap] {u} -> {e!r}")
    return None

async def get_domain_age(registered_domain: str, session) -> int | None:
    if not registered_domain:
        return None
    data = await fetch_rdap(registered_domain, session)
    if not data:
        return None
    reg = next((e["eventDate"] for e in data.get("events", [])
                if e.get("eventAction") == "registration"), None)
    if not reg:
        return None
    return (datetime.now(timezone.utc)
            - datetime.strptime(reg[:10], "%Y-%m-%d").replace(tzinfo=timezone.utc)).days

def describe_age(age: int) -> Finding:
    """User-specified ladder: <30d = hard red, 3mo = medium, 6mo = low, 1-2y = safe."""
    if age < 7:
        return Finding("Registered today" if age < 1 else f"Registered {age} day(s) ago", 70)
    if age < 30:
        return Finding(f"Registered {age} days ago", 60)
    if age < 90:
        return Finding(f"Registered {age // 30} month(s) ago", 35)
    if age < 180:
        return Finding(f"Registered {age // 30} months ago", 15)
    if age < 365:
        return Finding(f"Registered {age // 30} months ago", 5)
    if age < 730:
        return Finding(f"{age // 365}+ year(s) old", 0)
    return Finding(f"{age // 365}+ years old", -10)

# ---------------- domain-name checks ----------------
def check_brand(url: str) -> list[Finding]:
    ext = tldextract.extract(url)
    sld = (ext.domain or "").lower()
    sub = (ext.subdomain or "").lower()
    tier = tld_tier((ext.suffix or "").lower())
    out = []

    for brand in BRANDS:
        if brand == sld and tier in ("high_abuse", "elevated"):
            out.append(Finding(f'"{brand}" name on a scam-heavy TLD — fake', 30)); break
        if re.search(rf"\b{brand}\b", sld) and sld != brand:
            out.append(Finding(f'Impersonates "{brand}"', 35)); break
        if brand in sub.split("."):
            real = f"{ext.domain}.{ext.suffix}"
            out.append(Finding(f'"{brand}" only in subdomain — real site: {real}', 30)); break

    if not out:  # typosquats: paypa1, goggle, app1e
        compact = (sld.replace("-", "").replace("0", "o").replace("1", "l")
                      .replace("3", "e").replace("5", "s"))
        for brand in BRANDS:
            if len(brand) >= 5 and Levenshtein.distance(compact, brand) <= 2:
                out.append(Finding(f'Typosquat of "{brand}"', 30)); break
    return out

def check_semantics(url: str) -> list[Finding]:
    """Reads the domain name as language — catches scam-by-intent."""
    ext = tldextract.extract(url)
    sld = (ext.domain or "").lower()
    tokens = [t for t in re.split(r"[-_]+", sld) if t]
    brand_tokens = {t for t in tokens if t in BRANDS}
    kw_hits = {t for t in tokens if t in SCAM_KW}

    out = []
    combo_kw = kw_hits & (GAMBLING_KW | CRYPTO_KW)
    if brand_tokens and combo_kw:
        out.append(Finding(
            f"'{sorted(brand_tokens)[0]}' + '{sorted(combo_kw)[0]}' in domain — clone-site pattern", 20))
        return out
    if len(kw_hits) >= 2:
        out.append(Finding(f"Multiple red-flag words in domain: {', '.join(sorted(kw_hits))}", 18))
    elif len(kw_hits) == 1:
        out.append(Finding(f"Red-flag word in domain: '{sorted(kw_hits)[0]}'", 8))
    return out

def tld_tier(suffix: str) -> str:
    s = suffix.lower()
    last = s.split(".")[-1]
    if s in INSTITUTIONAL or last in INSTITUTIONAL:
        return "institutional"
    if s in MAINSTREAM or last in MAINSTREAM:
        return "mainstream"
    if s in HIGH_ABUSE or last in HIGH_ABUSE:
        return "high_abuse"
    if s in ELEVATED or last in ELEVATED:
        return "elevated"
    return "neutral"

def check_tld(url: str) -> list[Finding]:
    suffix = (tldextract.extract(url).suffix or "").lower()
    tier = tld_tier(suffix)
    tld = suffix.split(".")[-1]
    if tier == "high_abuse":
        return [Finding(f".{tld} — notorious for scams", 25)]
    if tier == "elevated":
        return [Finding(f".{tld} — cheap TLD, commonly abused", 10)]
    if tier == "institutional":
        return [Finding(f".{suffix} — official institutional registry", -10)]
    return []

# ---------------- VT / GSB ----------------
async def check_virustotal(url: str, session) -> list[Finding]:
    if not VT_API_KEY:
        return []
    url_id = base64.urlsafe_b64encode(url.encode()).decode().strip("=")
    headers = {"x-apikey": VT_API_KEY}
    try:
        async with session.get(f"https://www.virustotal.com/api/v3/urls/{url_id}",
                               headers=headers,
                               timeout=aiohttp.ClientTimeout(total=12)) as r:
            if r.status == 404:
                await session.post("https://www.virustotal.com/api/v3/urls",
                                   headers=headers, data={"url": url})
                return [Finding("VT scan queued (resend in 1 min)", 0)]
            if r.status == 429:
                return [Finding("VT rate-limited (retry in a minute)", 0)]
            if r.status != 200:
                print(f"[vt] {url} -> HTTP {r.status}")
                return []
            data = await r.json(content_type=None)
    except Exception as e:
        print(f"[vt] {url} -> {e!r}")
        return []

    attrs = data["data"]["attributes"]
    out = []
    stats = attrs.get("last_analysis_stats", {})
    bad = stats.get("malicious", 0) + stats.get("suspicious", 0)
    total = sum(stats.values()) or 1
    if bad:
        pts = 30 if bad >= 10 else 22 if bad >= 5 else 15 if bad >= 2 else 8
        out.append(Finding(f"Flagged by {bad}/{total} vendors", pts))

    cats = attrs.get("categories", [])
    if isinstance(cats, dict):
        cats = list(cats.keys())
    cats_l = [c.lower() for c in cats]
    if any(c in cats_l for c in ("phishing", "malicious", "malware")):
        out.append(Finding(f"VT categories: {', '.join(cats_l)}", 25))
    elif "scam/questionable" in cats_l:
        out.append(Finding(f"VT categories: {', '.join(cats_l)}", 15))
    elif "spam" in cats_l:
        out.append(Finding("VT category: spam", 8))
    elif "gambling" in cats_l:
        out.append(Finding("gambling category (VT)", 0))
    if bad == 0 and not out:
        out.append(Finding("clean in VT", 0))
    return out

async def check_safebrowsing(url: str, session) -> list[Finding]:
    if not GSB_API_KEY:
        return []
    body = {"client": {"clientId": "phishguard", "clientVersion": "0.3"},
            "threatInfo": {"threatTypes": ["MALWARE", "SOCIAL_ENGINEERING",
                                           "UNWANTED_SOFTWARE", "POTENTIALLY_HARMFUL_APPLICATION"],
                           "platformTypes": ["ANY_PLATFORM"],
                           "threatEntryTypes": ["URL"],
                           "threatEntries": [{"url": url}]}}
    try:
        async with session.post(
            f"https://safebrowsing.googleapis.com/v4/threatMatches:find?key={GSB_API_KEY}",
            json=body, timeout=aiohttp.ClientTimeout(total=12)) as r:
            data = await r.json(content_type=None)
    except Exception as e:
        print(f"[gsb] {url} -> {e!r}")
        return []
    kinds = {m["threatType"] for m in data.get("matches", [])}
    if kinds:
        label = "phishing" if "SOCIAL_ENGINEERING" in kinds else "malware"
        return [Finding(f"Google flags as {label}", 30)]
    return []

# ---------------- SSRF guard + SSL ----------------
async def host_forbidden(host: str) -> bool:
    """Never fetch/connect to private, loopback, or link-local targets."""
    def _bad(ip_str: str) -> bool:
        try:
            ip = ipaddress.ip_address(ip_str)
            return (ip.is_private or ip.is_loopback or ip.is_link_local
                    or ip.is_reserved or ip.is_multicast)
        except ValueError:
            return False
    if _bad(host):
        return True
    try:
        infos = await asyncio.get_running_loop().getaddrinfo(host, 443)
    except Exception:
        return False
    return any(_bad(info[4][0]) for info in infos)

async def check_ssl(host: str) -> list[Finding]:
    if not host or await host_forbidden(host):
        return []
    try:
        _, writer = await asyncio.wait_for(
            asyncio.open_connection(host, 443, ssl=ssl.create_default_context()), timeout=8)
    except ssl.SSLCertVerificationError:
        return [Finding("Invalid SSL certificate", 15)]
    except Exception:
        return [Finding("no HTTPS server", 0)]
    writer.close()
    return [Finding("valid SSL", 0)]

# ---------------- link shape + short links ----------------
def check_shape(url: str, host: str) -> list[Finding]:
    out = []
    try:
        ipaddress.ip_address(host)
        out.append(Finding("Bare IP address host", 15))
    except ValueError:
        pass
    ext = tldextract.extract(url)
    if f"{ext.domain}.{ext.suffix}" in SHORTENERS:
        out.append(Finding("Shortened link", 10))
    return out

async def resolve_shortlink(url: str, session) -> str | None:
    ext = tldextract.extract(url)
    if f"{ext.domain}.{ext.suffix}" not in SHORTENERS:
        return None
    host = (urlparse(url).hostname or "").lower()
    if not host or await host_forbidden(host):
        return None
    try:
        async with session.get(url, allow_redirects=True,
                               timeout=aiohttp.ClientTimeout(total=15)) as r:
            final = str(r.url)
            if final.rstrip("/") != url.rstrip("/"):
                print(f"[resolve] {url} -> {final}")
                return final
    except Exception as e:
        print(f"[resolve] {url} -> {e!r}")
    return None

# ---------------- CONTENT scanner ----------------
TITLE_RE = re.compile(r"<title[^>]*>(.*?)</title>", re.I | re.S)
SCRIPT_STYLE_RE = re.compile(r"<(script|style)\b[^>]*>.*?</\1>", re.I | re.S)
TAG_RE = re.compile(r"<[^>]+>")
PWD_RE = re.compile(r"type\s*=\s*[\"']?password", re.I)
REFRESH_RE_A = re.compile(r'http-equiv\s*=\s*["\']?refresh.*?content\s*=\s*["\']?\d+\s*;\s*url\s*=\s*([^"\'\s>]+)', re.I | re.S)
REFRESH_RE_B = re.compile(r'content\s*=\s*["\']?\d+\s*;\s*url\s*=\s*([^"\'\s>]+)[^>]*http-equiv\s*=\s*["\']?refresh', re.I | re.S)
EXE_TYPES = ("msdownload", "android.package-archive", "x-executable", "x-msi", "x-dosexec")

def check_content(url: str, html: str) -> tuple[list[Finding], dict]:
    title_m = TITLE_RE.search(html)
    title = title_m.group(1).strip() if title_m else ""
    body = re.sub(r"\s+", " ", TAG_RE.sub(" ", SCRIPT_STYLE_RE.sub(" ", html))).lower()
    t_low = title.lower()

    ext_c = tldextract.extract(url)
    sld_c = (ext_c.domain or "").lower()
    sub_c = (ext_c.subdomain or "").lower()

    meta = {
        "pwd_form": bool(PWD_RE.search(html)),
        "gambling": sum(k in body for k in CONTENT_GAMBLING),
        "bait": sum(k in body for k in CONTENT_BAIT),
        "drainer": sum(k in body for k in CONTENT_DRAINER),
        "freebait": sum(k in body for k in CONTENT_FREEBAIT),
        "title_brand": next((b for b in BRANDS
                             if b in t_low and b not in sld_c and b not in sub_c), None),
    }
    out: list[Finding] = []

    if meta["drainer"] >= 2 or (meta["drainer"] >= 1 and meta["pwd_form"]):
        out.append(Finding("Wallet seed/recovery phrase requested — drainer pattern", 40))
    elif meta["drainer"] == 1:
        out.append(Finding("Page mentions wallet recovery phrase", 12))

    if meta["bait"] >= 2:
        out.append(Finding("Urgency / verification-pressure language", 25 if meta["pwd_form"] else 12))
    elif meta["bait"] == 1 and meta["pwd_form"]:
        out.append(Finding("Verification pressure + password form", 15))

    if meta["gambling"] >= 2:
        out.append(Finding("Gambling content on page", 15))   # combo-boosted if domain is fresh

    if meta["freebait"] >= 2:
        out.append(Finding("Too-good-to-be-true offers on page", 12))

    my_dom = f"{sld_c}.{ext_c.suffix}".lower() if ext_c.suffix else ""
    m = REFRESH_RE_A.search(html) or REFRESH_RE_B.search(html)
    if m:
        d_ext = tldextract.extract(m.group(1))
        if d_ext.suffix:
            d_dom = f"{d_ext.domain}.{d_ext.suffix}".lower()
            if my_dom and d_dom != my_dom:
                out.append(Finding(f"Instantly auto-redirects to {d_dom}", 15))
    return out, meta

async def scan_content(url: str, session) -> tuple[list[Finding], dict]:
    host = (urlparse(url).hostname or "").lower()
    if not host or await host_forbidden(host):
        return [], {}
    try:
        async with session.get(url, headers=CONTENT_HEADERS,
                               timeout=aiohttp.ClientTimeout(total=12),
                               allow_redirects=True, max_redirects=5) as r:
            ctype = (r.headers.get("content-type") or "").lower()
            if any(x in ctype for x in EXE_TYPES):
                return [Finding("Serves a program file (.exe/.apk) — do not open", 40)], {}
            if "text/html" not in ctype:
                if "pdf" in ctype:
                    return [Finding("Serves a PDF — content not scanned", 0)], {}
                return [], {}
            raw = await r.content.read(600_000)
    except Exception as e:
        print(f"[fetch] {url} -> {e!r}")
        return [Finding("Page unreadable (offline, blocked, or bot-protection)", 0)], {}
    return check_content(url, raw.decode("utf-8", "ignore"))

# ---------------- pipeline + scoring ----------------
def normalize(raw: str) -> str:
    url = raw.strip()
    if not url.startswith(("http://", "https://")):
        url = "http://" + url
    return url

def display_domain(url: str) -> str:
    ext = tldextract.extract(url)
    return f"{ext.domain}.{ext.suffix}".lower() if ext.suffix else (urlparse(url).hostname or url)

async def analyze(raw: str) -> str:
    url = normalize(raw)
    resolved_from = None
    async with aiohttp.ClientSession(headers=HEADERS) as session:
        dest = await resolve_shortlink(url, session)
        if dest:
            resolved_from = display_domain(url)
            url = dest
        host = (urlparse(url).hostname or "").lower()
        ext = tldextract.extract(url)
        registered_domain = f"{ext.domain}.{ext.suffix}".lower() if ext.suffix else ""

        age, gsb_r, vt_r, ssl_r, content_r = await asyncio.gather(
            get_domain_age(registered_domain, session),
            check_safebrowsing(url, session),
            check_virustotal(url, session),
            check_ssl(host),
            scan_content(url, session),
            return_exceptions=True,
        )

    findings: list[Finding] = []
    for r in (gsb_r, vt_r, ssl_r):
        if isinstance(r, list):
            findings += [f for f in r if isinstance(f, Finding)]

    age_val = age if isinstance(age, int) else None
    if age_val is not None:
        findings.append(describe_age(age_val))
    else:
        if isinstance(age, BaseException):
            print(f"[age] {raw} -> {age!r}")
        findings.append(Finding("domain age unavailable", 0))

    c_find, c_meta = ([], {})
    if isinstance(content_r, tuple):
        c_find, c_meta = content_r
    elif isinstance(content_r, BaseException):
        print(f"[content] {raw} -> {content_r!r}")
    findings += c_find

    # ---- combo rules: weak signals combine into strong ones ----
    if age_val is not None and age_val < 90 and c_meta.get("gambling", 0) >= 2:
        findings.append(Finding("Brand-new domain promoting gambling — scam profile", 30))
    if age_val is not None and age_val < 30 and c_meta.get("pwd_form"):
        findings.append(Finding("Password form on a brand-new domain", 20))
    if c_meta.get("pwd_form") and c_meta.get("title_brand"):
        tb = c_meta["title_brand"]
        findings.append(Finding(f"Password form uses '{tb}' branding on an unrelated domain", 30))
    if age_val is not None and age_val < 30:
        for f in findings:
            if "gambling category" in f.text:
                f.points = max(f.points, 15)
                f.text = "Brand-new gambling site — high-risk combination"

    findings += check_brand(url) + check_semantics(url) + check_shape(url, host) + check_tld(url)
    if resolved_from:
        findings.append(Finding(f"Resolved from {resolved_from}", 10))
    score = max(0, min(100, sum(f.points for f in findings)))
    return render(url, findings, score)

def render(url: str, findings: list[Finding], score: int) -> str:
    domain = display_domain(url)
    problems = sorted((f for f in findings if f.points > 0), key=lambda x: -x.points)
    others = [f for f in findings if f.points <= 0]

    for f in problems:
        f.icon = "🚨" if f.points >= 30 else "⚠️" if f.points >= 15 else "🟡"

    top = problems[0].points if problems else 0
    if score >= 60:
        head, verdict, footer = "🔴", "HIGH RISK", \
            "👉 <b>Don't open it.</b> Don't enter any info — report it as phishing."
    elif score >= 30 or top >= 30:
        head, verdict, footer = "🟠", "SUSPICIOUS", \
            "👉 Open the official site/app yourself instead of this link."
    else:
        head, verdict, footer = "🟢", "LOW RISK", \
            ("🤖 Nothing conclusive — but note the signals above." if problems
             else "🤖 No scanner is perfect — stay alert anyway.")

    lines = [f"{head} <b>{verdict} · {score}/100</b>", f"🔗 <b>{escape(domain)}</b>"]
    if problems:
        lines.append("")
        lines += [f"{f.icon} {escape(f.text)}" for f in problems]
    if others:
        lines.append(f"\n✅ {escape(' · '.join(f.text for f in others))}")
    lines += ["", footer]
    return "\n".join(lines)

# ---------------- telegram bot ----------------
bot = Bot(TELEGRAM_TOKEN, default=DefaultBotProperties(parse_mode=ParseMode.HTML))
dp = Dispatcher()
CACHE: dict[str, tuple[float, str]] = {}
TTL = 600
WARNED: dict[tuple[int, str], float] = {}

async def quick_report(raw: str) -> str:
    """Instant offline checks only (inline queries must answer fast)."""
    if raw in CACHE and time.time() - CACHE[raw][0] < TTL:
        return CACHE[raw][1]
    url = normalize(raw)
    host = (urlparse(url).hostname or "").lower()
    findings = check_brand(url) + check_semantics(url) + check_shape(url, host) + check_tld(url)
    score = max(0, min(100, sum(f.points for f in findings)))
    return render(url, findings, score)

@dp.message(CommandStart())
async def start(m: Message):
    await m.answer("🛡 <b>PhishGuard</b> — send me a link, I'll tell you if it looks like a scam.\n\n"
                   "I check the domain (age, brand impersonation, typosquats, TLD reputation), "
                   "<b>read the page itself</b> (gambling content, fake login forms, wallet drainers, "
                   "pressure tactics), plus VirusTotal & Google Safe Browsing.\n\n"
                   "🔒 Nothing you send is stored.")

@dp.message(F.text, F.chat.type == "private")
async def handle(m: Message):
    urls = [u for u in URL_RE.findall(m.text or "")
            if not u.lower().startswith(("t.me/", "telegram.me"))]
    if not urls:
        await m.answer("Send me a link 🔎 — e.g. <code>paypal-secure-login.xyz</code>")
        return
    status = await m.answer("⏳ Checking…")
    raw = urls[0]
    cached = CACHE.get(raw)
    if cached and time.time() - cached[0] < TTL:
        report = cached[1]
    else:
        try:
            report = await asyncio.wait_for(analyze(raw), timeout=45)
        except Exception as e:
            print(f"[analyze] {raw} -> {e!r}")
            report = "😵 Check failed — try again."
        CACHE[raw] = (time.time(), report)
    await status.edit_text(report)

@dp.message(F.text, F.chat.type.in_({"group", "supergroup"}))
async def group_scan(m: Message):
    urls = [u for u in URL_RE.findall(m.text or "")
            if not u.lower().startswith(("t.me/", "telegram.me"))]
    if not urls:
        return
    raw = urls[0]
    key = (m.chat.id, raw)
    if key in WARNED and time.time() - WARNED[key] < 3600:
        return
    cached = CACHE.get(raw)
    if cached and time.time() - cached[0] < TTL:
        report = cached[1]
    else:
        try:
            report = await asyncio.wait_for(analyze(raw), timeout=45)
        except Exception:
            return
        CACHE[raw] = (time.time(), report)
    if "🔴" in report or "🟠" in report:
        WARNED[key] = time.time()
        await m.reply(report)

@dp.inline_query()
async def inline_scan(inline_q: InlineQuery):
    query = inline_q.query.strip()
    match = URL_RE.search(query)
    if not match:
        await inline_q.answer([], cache_time=5)
        return
    raw = match.group(0)
    try:
        report = await asyncio.wait_for(quick_report(raw), timeout=8)
    except Exception:
        report = "😵 Check failed — send the link to the bot directly."
    await inline_q.answer(
        [InlineQueryResultArticle(
            id=uuid.uuid4().hex,
            title="🛡 Check this link",
            description=raw[:64],
            input_message_content=InputTextMessageContent(
                message_text=report, parse_mode=ParseMode.HTML))],
        cache_time=300)

async def main():
    print("✅ PhishGuard is running")
    print(f"   VirusTotal:      {'ENABLED' if VT_API_KEY else 'DISABLED'}")
    print(f"   Safe Browsing:   {'ENABLED' if GSB_API_KEY else 'DISABLED'}")
    print("   Content scanner: ENABLED (reads pages)")
    await dp.start_polling(bot)

if __name__ == "__main__":
    asyncio.run(main())
