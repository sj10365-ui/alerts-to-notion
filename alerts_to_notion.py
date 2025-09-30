# alerts_to_notion.py
import os, re, time, json, logging, unicodedata, html
from datetime import datetime, timedelta, timezone
from urllib.parse import urlparse, urlunparse, parse_qsl, urlencode

import feedparser, requests
from rapidfuzz import fuzz
from dotenv import load_dotenv

# =================== BOOT ===================
load_dotenv()
logging.basicConfig(level=logging.INFO)

# =================== ENV ===================
NOTION_TOKEN        = os.getenv("NOTION_TOKEN", "").strip()
NOTION_DATABASE_ID  = os.getenv("NOTION_DATABASE_ID", "").strip()

def _parse_feed_urls(raw: str):
    out = []
    for part in (raw or "").splitlines():
        for u in part.split(","):
            u = u.strip()
            if u:
                out.append(u)
    return out
FEED_URLS           = _parse_feed_urls(os.getenv("FEED_URLS",""))

LOOKBACK_HOURS      = int(os.getenv("LOOKBACK_HOURS", "168"))
MAX_ITEMS           = int(os.getenv("MAX_ITEMS", "60"))
SIMILARITY_THRESHOLD= int(os.getenv("SIMILARITY_THRESHOLD", "80"))
MAX_PER_DOMAIN      = int(os.getenv("MAX_PER_DOMAIN", "5"))  # 0=제한 없음
DRY_RUN             = os.getenv("DRY_RUN","1") == "1"
DEBUG_DUMP          = os.getenv("DEBUG_DUMP","0") == "1"

ONLY_NEW            = os.getenv("ONLY_NEW","1") == "1"
SEEN_FILE           = os.getenv("SEEN_FILE","./.seen_urls.json")
SEEN_TTL_DAYS       = int(os.getenv("SEEN_TTL_DAYS","60"))

def _json_obj(env_key, default_obj):
    try:
        raw = os.getenv(env_key, "")
        return json.loads(raw) if raw else default_obj
    except Exception:
        return default_obj

# 랭킹 가중치(선호/패널티) - 환경변수 JSON로 주입 가능
FAVOR_WEIGHTS       = _json_obj("FAVOR_WEIGHTS", {})
DOWNWEIGHT_WEIGHTS  = _json_obj("DOWNWEIGHT_WEIGHTS", {})

# 카테고리/출처 분류 사전 파일 경로
KEYWORD_CATEGORY_FILE   = os.getenv("KEYWORD_CATEGORY_FILE","").strip()               # {"키워드":"카테고리"}
SOURCE_TYPE_MAP_FILE    = os.getenv("SOURCE_TYPE_MAP_FILE","dictionary/source_type_map.json").strip()  # {"자사":[...],"경쟁사":[...], "업계":[...]}

# ── 요약 고도화 옵션 ─────────────────────────────
USE_FULLTEXT       = os.getenv("USE_FULLTEXT","1") == "1"   # 페이지 본문 가져와 요약
FULLTEXT_TIMEOUT   = int(os.getenv("FULLTEXT_TIMEOUT","8")) # 초
SUMMARY_MAX_CHARS  = int(os.getenv("SUMMARY_MAX_CHARS","500"))

# ── 도메인 필터 (JSON 문자열로 입력) ─────────────
def _json_set(env_key):
    try:
        raw = os.getenv(env_key,"").strip()
        return set(json.loads(raw)) if raw else set()
    except Exception:
        return set()

DOMAIN_ALLOW = _json_set("DOMAIN_ALLOW")  # 비워두면 전체 허용
DOMAIN_BLOCK = _json_set("DOMAIN_BLOCK")  # 여기에 있으면 제거

# 필수값 체크
assert NOTION_TOKEN, "NOTION_TOKEN 필요"
assert NOTION_DATABASE_ID, "NOTION_DATABASE_ID 필요(하이픈 없는 32자리)"
assert FEED_URLS, "FEED_URLS 필요(Variables/Secrets에 URL 목록)"

# ── 경쟁사 기사 주류 키워드 강제 여부 ─────────────
REQUIRE_LIQUOR_FOR_COMP = os.getenv("REQUIRE_LIQUOR_FOR_COMP","1") == "1"
COMP_LIQUOR_REGEX = re.compile(
    os.getenv(
        "COMP_LIQUOR_REGEX",
        r"(주류|술|위스키|하이볼|버번|스카치|싱글\s*몰트|블렌디드|"
        r"와인|샴페인|스파클링|사케|니혼슈|일본주|"
        r"맥주|수제맥주|라거|에일|\bIPA\b|크래프트\s*비어|"
        r"전통주|막걸리|탁주|약주|증류주|리큐르|RTD)"
    ),
    re.IGNORECASE,
)

# =================== UTIL / NORMALIZE ===================

# 추한 HTML 엔티티/스마트 따옴표/대시 등 통일
CHAR_REPLACE = {
    "\u2018": "'",  # ‘
    "\u2019": "'",  # ’
    "\u201C": '"',  # “
    "\u201D": '"',  # ”
    "\u2013": "-",  # –
    "\u2014": "-",  # —
    "\u00A0": " ",  # nbsp
    "\u200b": "",   # zero width space
}

# 기사 말미 보일러플레이트/저작권/구독/쿠키 안내 제거
BOILERPLATE_PATTERNS = [
    r"무단\s*전재\s*및\s*재배포\s*금지.*$",
    r"본\s*기사는.*?저작권.*?보호.*$",
    r"구독|광고문의|제보하기|뉴스레터\s*구독.*$",
    r"쿠키(를|가)\s*허용|브라우저.*(설정|지원).*$",
    r"Copyright\s*©.*$",
    r"ⓒ.*(신문|뉴스|미디어).*$",
]

TRACKING_PARAMS = {
    "utm_source","utm_medium","utm_campaign","utm_term","utm_content",
    "utm_name","utm_id","utm_reader","utm_cid","utm_referrer",
    "fbclid","gclid","msclkid","igshid","ved","ei","oq","aqs","sclient"
}

def _apply_char_replace(s: str) -> str:
    if not s: return s
    for k,v in CHAR_REPLACE.items():
        s = s.replace(k, v)
    return s

def _strip_boilerplate(s: str) -> str:
    if not s: return s
    for pat in BOILERPLATE_PATTERNS:
        s = re.sub(pat, "", s, flags=re.IGNORECASE)
    return s.strip()

def domain_of(url:str)->str:
    try:
        host = urlparse(url).netloc.lower()
        return host[4:] if host.startswith("www.") else host
    except:
        return ""

def normalize_text(t:str)->str:
    # 1) 태그 제거
    t = re.sub(r"<[^>]+>", " ", t or "")
    # 2) 엔티티 해제(두 번 안전하게)
    t = html.unescape(html.unescape(t))
    # 3) 스마트 따옴표/대시/공백 정리
    t = _apply_char_replace(t)
    # 4) 여백 압축
    t = re.sub(r"\s+", " ", t).strip()
    # 5) 말미 보일러플레이트 제거
    t = _strip_boilerplate(t)
    return t

def _unwrap_google_url(url:str)->str:
    try:
        u = urlparse(url)
        # Google Alerts가 종종 /url?rct=… 형태로 감싸서 줌
        if u.netloc.endswith("google.com") and u.path == "/url":
            q = dict(parse_qsl(u.query, keep_blank_values=True))
            return q.get("url") or q.get("q") or url
        return url
    except:
        return url

def canonicalize_url(url:str)->str:
    try:
        raw = _unwrap_google_url(url)
        u = urlparse(raw)
        q = [(k,v) for k,v in parse_qsl(u.query, keep_blank_values=True)
             if k.lower() not in TRACKING_PARAMS]
        return urlunparse((u.scheme, u.netloc.lower(), u.path, "", urlencode(q), ""))
    except:
        return url

BRACKET_PATTERNS = [r"\[[^\]]+\]", r"\([^)]+\)", r"【[^】]+】"]
def normalize_title(t:str)->str:
    t = unicodedata.normalize("NFKC", t or "")
    t = html.unescape(html.unescape(t))
    t = _apply_char_replace(t)
    for p in BRACKET_PATTERNS:
        t = re.sub(p, " ", t)
    t = re.sub(r"\s+", " ", t).strip()
    # 제목도 불필요 꼬리표 제거(‘…| 언론사명’같은 것)
    t = re.sub(r"\s*[-|]\s*(사진|포토|영상|단독|속보)\s*$", "", t)
    return t.lower()

def dump(items, label, n=20):
    if not DEBUG_DUMP: return
    print(f"\n=== {label} ({len(items)} items) ===")
    for it in items[:n]:
        ts = it["published"].astimezone(timezone(timedelta(hours=9))).strftime("%m-%d %H:%M")
        print(f"{ts} | {it['domain']:<22} | {it['title']}")
    print("============================")

# =================== FULLTEXT & SUMMARY ===================
def fetch_article_text(url: str, timeout: int = 8) -> str:
    """
    가벼운 휴리스틱 본문 추출:
    - script/style/nav/footer 제거
    - <p> 텍스트 밀도가 높은 덩어리 선호
    """
    try:
        res = requests.get(url, timeout=timeout, headers={
            "User-Agent": "Mozilla/5.0 (compatible; AlertsToNotion/1.0)"
        })
        if not res.ok:
            return ""
        doc = res.text

        doc = re.sub(r"(?is)<script[^>]*>.*?</script>", " ", doc)
        doc = re.sub(r"(?is)<style[^>]*>.*?</style>", " ", doc)
        doc = re.sub(r"(?is)<nav[^>]*>.*?</nav>", " ", doc)
        doc = re.sub(r"(?is)<footer[^>]*>.*?</footer>", " ", doc)
        doc = re.sub(r"(?is)<!--.*?-->", " ", doc)

        paras = re.findall(r"(?is)<p[^>]*>(.*?)</p>", doc)
        texts = []
        for p in paras:
            t = re.sub(r"<[^>]+>", " ", p)
            t = normalize_text(t)
            if len(t) >= 40:
                texts.append(t)

        texts = sorted(texts, key=len, reverse=True)[:25]
        body = " ".join(texts)
        return normalize_text(body)
    except Exception:
        return ""

def make_summary(title: str, feed_snippet: str, fulltext: str, limit: int = 500) -> str:
    """
    - 풀텍스트가 있으면 2~3문장 요약
    - 없으면 RSS snippet 1~2문장 정리
    """
    def clean(s: str) -> str:
        s = normalize_text(s)
        # 추가로 제목 반복/형식 꼬임 정돈
        s = re.sub(r"^\W*"+re.escape((title or "").strip())+r"\W*", "", s, flags=re.IGNORECASE)
        return s.strip()

    if fulltext:
        sents = re.split(r"(?<=[\.!?。])\s+", fulltext)
        pick = []
        for s in sents:
            s = clean(s)
            if (3 <= len(s) <= 300) and not re.search(r"(쿠키|브라우저|로그인|구독|광고)", s):
                pick.append(s)
            if len(" ".join(pick)) > limit * 0.8:
                break
        summary = " ".join(pick[:3])
    else:
        summary = clean(feed_snippet)

    if len(summary) > limit:
        summary = summary[:limit-1] + "…"
    return summary or "(요약 없음)"

# =================== CATEGORY ===================
def _load_keyword_map():
    if KEYWORD_CATEGORY_FILE and os.path.exists(KEYWORD_CATEGORY_FILE):
        try:
            with open(KEYWORD_CATEGORY_FILE, "r", encoding="utf-8") as f:
                return json.load(f)  # {"키워드":"카테고리"}
        except Exception as e:
            logging.warning(f"keyword map load failed: {e}")
    return {}
KEYWORD_CATEGORY_MAP = _load_keyword_map()

CAT_ORDER = ["위스키","와인","사케","맥주","전통주","기타"]
CAT_PATTERNS = [
    ("위스키",  [r"위스키", r"하이볼", r"스카치", r"버번", r"싱글\s*몰트", r"블렌디드"]),
    ("와인",    [r"와인", r"레드와인", r"화이트와인", r"스파클링", r"샴페인"]),
    ("사케",    [r"사케", r"니혼슈", r"일본주"]),
    ("맥주",    [r"맥주", r"수제맥주", r"크래프트\s*비어", r"라거", r"에일", r"\bIPA\b"]),
    ("전통주",  [r"전통주", r"우리술", r"막걸리", r"탁주", r"약주"]),
]
def _cat_priority(cat:str)->int:
    return CAT_ORDER.index(cat) if cat in CAT_ORDER else len(CAT_ORDER)

def categorize(title:str, summary:str="")->str:
    tl=(title or "").lower(); sl=(summary or "").lower()
    best=None  # (len_kw, -priority, cat)
    for kw, cat in (KEYWORD_CATEGORY_MAP or {}).items():
        k=(kw or "").lower().strip()
        if not k: continue
        if k in tl or k in sl:
            cand=(len(k), -_cat_priority(cat), cat)
            if (best is None) or (cand > best):
                best = cand
    if best: return best[2]
    for label, pats in CAT_PATTERNS:
        for p in pats:
            if re.search(p, tl) or re.search(p, sl):
                return label
    return "기타"

# =================== SOURCE TYPE (자사/경쟁사/업계) ===================
def _load_source_type_map(path: str):
    try:
        if os.path.exists(path):
            with open(path, "r", encoding="utf-8") as f:
                raw = json.load(f)
        else:
            raw = {}
        norm = {bucket: [kw.lower() for kw in kws] for bucket, kws in raw.items()}
        for b in ("자사","경쟁사","업계"):
            norm.setdefault(b, [])
        return norm
    except Exception as e:
        logging.warning(f"source_type map load failed: {e}")
        return {"자사": [], "경쟁사": [], "업계": []}

SOURCE_TYPE_MAP = _load_source_type_map(SOURCE_TYPE_MAP_FILE)

def classify_source_type(item: dict) -> str:
    hay = " ".join([
        str(item.get("title","")),
        str(item.get("summary","")),
        str(item.get("domain","")),
        str(item.get("link","")),
    ]).lower()
    hay = re.sub(r"\s+", " ", hay)
    for bucket in ("자사","경쟁사","업계"):
        for kw in SOURCE_TYPE_MAP.get(bucket, []):
            if kw and kw in hay:
                return bucket
    dom = (item.get("domain") or "").lower()
    if any(x in dom for x in ["co.kr","com","go.kr","or.kr"]):
        return "업계"
    return "업계"

# =================== FETCH ===================
def fetch_all(feeds):
    rows=[]
    for url in feeds:
        d=feedparser.parse(url)
        for e in d.entries:
            ts_struct = e.get("published_parsed") or e.get("updated_parsed")
            ts = datetime.fromtimestamp(time.mktime(ts_struct), tz=timezone.utc) if ts_struct else datetime.now(timezone.utc)
            link = canonicalize_url(getattr(e, "link", ""))
            title_raw = getattr(e, "title", "")
            summary_raw = getattr(e, "summary", "")

            # 정규화 적용
            title = normalize_text(title_raw)
            summary = normalize_text(summary_raw)[:800]

            rows.append({
                "title": title,
                "summary": summary,
                "link": link,
                "published": ts,
                "domain": domain_of(link) or "google.com",
            })
    return rows

# =================== RANK (가중치 + 시간) ===================
BASE_UNIT = 1_000_000
def weighted_score(it):
    base = it["published"].timestamp()
    t = (it["title"] or "").lower()
    bonus = 0
    for kw, w in FAVOR_WEIGHTS.items():
        try: bonus += t.count(kw.lower()) * int(w) * BASE_UNIT
        except: pass
    for kw, w in DOWNWEIGHT_WEIGHTS.items():
        try: bonus += t.count(kw.lower()) * int(w) * BASE_UNIT
        except: pass
    return base + bonus
# -------- 핵심 제목 클러스터링 --------
COMPANY_WORDS = [
    "이마트", "이마트24", "emart24", "롯데", "롯데백화점", "신세계", "gs25",
    "세븐일레븐", "cu", "하이트진로", "롯데칠성", "오비맥주", "아영fbc",
    "문배주", "국순당", "골든블루"
]
STOP_TOKENS = ["단독","속보","포토","영상","종합","인터뷰","발표","진행","출시","행사","페스티벌","페스타"]

def core_title_key(title: str) -> str:
    t = title or ""
    t = re.sub(r"[^\w가-힣\s]", " ", t, flags=re.UNICODE)       # 기호 제거
    t = re.sub(r"\d{1,4}[./-]\d{1,2}[./-]\d{1,2}", " ", t)      # 날짜 제거
    t = re.sub(r"\d[\d,\.]*", " ", t)                           # 숫자 제거
    t = t.lower()
    for w in COMPANY_WORDS:
        t = re.sub(rf"\b{re.escape(w.lower())}\b", " ", t)
    for w in STOP_TOKENS:
        t = re.sub(rf"\b{re.escape(w.lower())}\b", " ", t)
    t = re.sub(r"\s+", " ", t).strip()
    # 너무 짧으면 원제목으로 fallback
    return t if len(t) >= 6 else (title or "").lower()

def collapse_by_core_title(items: list) -> list:
    """
    핵심 제목 키로 클러스터링해서 각 그룹의 최고 점수 1개만 유지
    """
    buckets = {}
    for it in items:
        key = core_title_key(it["title"])
        score = weighted_score(it)
        cur = buckets.get(key)
        if (cur is None) or (score > cur[0]):
            buckets[key] = (score, it)
    return [v[1] for v in buckets.values()]
    
# =================== DEDUPE ===================
def dedupe_similar(items, threshold=80, max_per_domain=5):
    kept=[]; seen_per_dom={}
    for it in items:
        t_new = normalize_title(it["title"])
        url_new = canonicalize_url(it["link"])
        dom = it["domain"]
        if max_per_domain>0 and seen_per_dom.get(dom,0) >= max_per_domain:
            continue
        dup=False
        for kt in kept:
            if canonicalize_url(kt["link"]) == url_new:
                dup=True; break
            if fuzz.token_set_ratio(t_new, normalize_title(kt["title"])) >= threshold:
                dup=True; break
        if not dup:
            kept.append(it)
            seen_per_dom[dom] = seen_per_dom.get(dom,0) + 1
    return kept

# =================== SEEN CACHE (ONLY_NEW) ===================
def load_seen(path:str)->dict:
    try:
        if os.path.exists(path):
            with open(path,"r",encoding="utf-8") as f:
                return json.load(f)
    except Exception as e:
        logging.warning(f"seen load failed: {e}")
    return {}

def save_seen(path:str, data:dict):
    try:
        with open(path,"w",encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
    except Exception as e:
        logging.warning(f"seen save failed: {e}")

def prune_seen(seen:dict, ttl_days:int):
    try:
        cutoff = datetime.now(timezone.utc) - timedelta(days=ttl_days)
        keys=[]
        for k,v in seen.items():
            try:
                ts = datetime.fromisoformat(v.get("last_seen"))
            except Exception:
                ts = None
            if (ts is None) or (ts < cutoff):
                keys.append(k)
        for k in keys: seen.pop(k, None)
    except Exception as e:
        logging.warning(f"seen prune failed: {e}")

def key_for_item(it:dict)->str:
    return canonicalize_url(it.get("link",""))

def mark_seen(seen:dict, it:dict):
    k = key_for_item(it)
    now_iso = datetime.now(timezone.utc).isoformat()
    if k not in seen:
        seen[k] = {"first_seen": now_iso, "last_seen": now_iso, "title": it.get("title",""), "domain": it.get("domain","")}
    else:
        seen[k]["last_seen"] = now_iso

# =================== NOTION ===================
def notion_create_page(it, cat:str, source_type:str):
    url="https://api.notion.com/v1/pages"
    safe_token = re.sub(r"[^\x20-\x7E]", "", (NOTION_TOKEN or "")).strip()
    headers={
        "Authorization": f"Bearer {safe_token}",
        "Notion-Version": "2022-06-28",
        "Content-Type": "application/json"
    }
    data={
        "parent":{"database_id": NOTION_DATABASE_ID},
        "properties":{
            # 노션 DB 속성명: Title / Link / Summary / Source / Published / Category / SourceType
            "Title":{"title":[{"text":{"content": (it["title"] or "(no title)")[:200]}}]},
            "Link":{"url": (it["link"] or "")[:2000]},
            "Summary":{"rich_text":[{"text":{"content": (it.get("summary",""))[:1800]}}]},
            "Source":{"rich_text":[{"text":{"content": (it["domain"] or "")[:200]}}]},
            "Published":{"date":{"start": it["published"].astimezone(timezone.utc).isoformat() }},
            "Category":{"select":{"name": cat or "기타"}},
        }
    }
    if source_type:
        data["properties"]["SourceType"] = {"select": {"name": source_type}}

    r = requests.post(url, headers=headers, json=data, timeout=20)
    if not r.ok:
        logging.error(f"Notion error: {r.text}")
    return r.ok

# =================== MAIN ===================
def main():
    now = datetime.now(timezone.utc)
    cutoff = now - timedelta(hours=LOOKBACK_HOURS)

    all_items = fetch_all(FEED_URLS); logging.info(f"fetched {len(all_items)}"); dump(all_items,"FETCH")
    filtered = [it for it in all_items if it["published"] >= cutoff]; logging.info(f"time filter {len(filtered)}"); dump(filtered,"FILTERED")

    # ── 도메인 허용/차단 적용 ───────────────────────
    if DOMAIN_BLOCK:
        before = len(filtered)
        filtered = [it for it in filtered if it["domain"] not in DOMAIN_BLOCK]
        logging.info(f"domain block: {before} -> {len(filtered)} (blocked={len(DOMAIN_BLOCK)})")

    if DOMAIN_ALLOW:
        before = len(filtered)
        filtered = [it for it in filtered if it["domain"] in DOMAIN_ALLOW]
        logging.info(f"domain allow: {before} -> {len(filtered)} (allow-only)")
        
    # ── 경쟁사 기사 가드: 주류 관련 키워드 없으면 컷 ─────────
    if REQUIRE_LIQUOR_FOR_COMP:
        before = len(filtered)
        kept = []
        for it in filtered:
            src_type = classify_source_type(it)
            if src_type == "경쟁사":
                text = f"{it.get('title','')} {it.get('summary','')}"
                # 1) 주류 키워드 정규식 매칭 OR 2) 카테고리 분류가 '기타'가 아닐 때만 통과
                has_liquor_kw = bool(COMP_LIQUOR_REGEX.search(text))
                cat = categorize(it.get("title",""), it.get("summary",""))
                if not has_liquor_kw and cat == "기타":
                    continue
            kept.append(it)
        filtered = kept
        logging.info(f"competitor guard: {before} -> {len(filtered)}")
        
    # 소량 보정: 표본이 적을 때 느슨화
    if len(filtered) < 25:
        extra_cutoff = now - timedelta(hours=LOOKBACK_HOURS * 2)
        filtered = [it for it in all_items if it["published"] >= extra_cutoff]
        logging.info(f"low volume → extended lookback: {len(filtered)} items")

    ranked = sorted(filtered, key=weighted_score, reverse=True); dump(ranked,"RANKED")
    # 핵심 제목 기준 1차 클러스터링(동일 보도자료 싱딕·브랜드 반복 축소)
    ranked = collapse_by_core_title(ranked)

    th = SIMILARITY_THRESHOLD
    cap = MAX_PER_DOMAIN
    if len(ranked) < 20:
        th = max(75, SIMILARITY_THRESHOLD - 5)
        cap = max(5, MAX_PER_DOMAIN)
        logging.info(f"low volume → relax dedupe: th={th}, cap={cap}")

    uniq = dedupe_similar(ranked, threshold=th, max_per_domain=cap); logging.info(f"deduped {len(uniq)}"); dump(uniq,"DEDUPED")

    # 신규만 남기기
    seen = load_seen(SEEN_FILE)
    prune_seen(seen, SEEN_TTL_DAYS)
    if ONLY_NEW:
        before = len(uniq)
        uniq = [it for it in uniq if key_for_item(it) not in seen]
        logging.info(f"history dedupe: {before} -> {len(uniq)} (ONLY_NEW={ONLY_NEW})")

    items = uniq[:MAX_ITEMS]

    # ── 요약 고도화: 본문 크롤링 후 자연 요약 ─────────
    if USE_FULLTEXT and items:
        for it in items:
            try:
                full = fetch_article_text(it["link"], timeout=FULLTEXT_TIMEOUT)
                it["summary"] = make_summary(it["title"], it.get("summary",""), full, limit=SUMMARY_MAX_CHARS)
            except Exception as e:
                logging.warning(f"fulltext/summary failed: {e}")

    if DRY_RUN:
        print("\n=== DRY RUN (to be written) ===")
        for it in items:
            cat = categorize(it["title"], it.get("summary",""))
            src_type = classify_source_type(it)
            print(f"- [{cat}][{src_type}] {it['title']} ({it['domain']}) {it['link']}")
            mark_seen(seen, it)  # 미리보기에서도 ‘본 것으로’ 처리하려면 유지
        save_seen(SEEN_FILE, seen)
        print("===============================\n")
        return

    ok=0; fail=0
    for it in items:
        cat = categorize(it["title"], it.get("summary",""))
        src_type = classify_source_type(it)
        if notion_create_page(it, cat, src_type):
            ok+=1
            mark_seen(seen, it)   # 성공한 것만 기록
        else:
            fail+=1
    save_seen(SEEN_FILE, seen)
    logging.info(f"Notion write done: ok={ok}, fail={fail}")

if __name__ == "__main__":
    main()
