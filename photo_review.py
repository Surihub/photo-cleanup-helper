#!/usr/bin/env python3
"""
사진 정리 도우미 (Photo Review)

MacBook의 사진 앱 보관함을 읽어, 용량을 줄이기 위해 지울 만한 후보를 찾아
브라우저 화면으로 보여 준다. iPhone 사진을 iCloud 사진으로 쓰고 있다면
MacBook 사진 앱과 iPhone이 같은 보관함을 쓰므로, 여기서 정리한 결과가
iPhone에도 그대로 반영된다.

동작 방식
1. 보관함 데이터베이스(Photos.sqlite)를 읽기 전용으로 열어 항목 목록을 메모리에 올린다.
2. 이 컴퓨터(127.0.0.1)에서만 접속되는 웹 서버를 띄우고 web/index.html 화면을 제공한다.
3. 화면에서 고른 항목은 사진 앱의 새 앨범에 모으거나, 원본을 다른 폴더로 복사하거나,
   CSV로 저장할 수 있다. 실제 삭제는 사용자가 사진 앱에서 직접 한다.

안전 원칙
- 사진 보관함 데이터베이스는 읽기 전용(immutable)으로만 연다.
- 이 프로그램에는 사진을 삭제하는 코드가 없다.
- 보관함에 대한 쓰기는 사용자가 버튼을 눌렀을 때 '사진 앱에 앨범 만들기' 한 가지뿐이며,
  이것도 사진 앱의 AppleScript 기능으로 앨범을 추가하는 데 그친다.
- '원본 내보내기'는 사진을 복사만 한다.

주의
- Photos.sqlite의 구조는 Apple이 공개한 형식이 아니다. 아래 쿼리의 열 이름과 값의 의미는
  실제 보관함에서 확인한 것이며, macOS 버전에 따라 달라질 수 있다.
- 앨범 만들기와 원본 내보내기는 AppleScript로 사진 앱을 제어하므로, 처음 실행할 때
  macOS의 '자동화' 권한 허용이 필요하다.

실행
    python3 photo_review.py [--library 보관함_경로] [--port 8765] [--no-browser]

macOS 전용이며, 파이썬 표준 라이브러리만 사용한다(별도 설치 불필요, Python 3.8 이상).
"""
import argparse
import csv
import json
import os
import re
import shutil
import sqlite3
import subprocess
import sys
import tempfile
import threading
import time
import uuid as uuidlib
import webbrowser
from collections import defaultdict
from datetime import datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, quote, urlparse

APP_DIR = os.path.dirname(os.path.abspath(__file__))
WEB_DIR = os.path.join(APP_DIR, "web")          # 화면 파일(index.html, noimage.svg) 위치
DEFAULT_LIBRARY = os.path.expanduser("~/Pictures/Photos Library.photoslibrary")
APPLE_EPOCH = 978307200  # 2001-01-01 UTC. 사진 앱의 시각은 이 시점부터의 초로 저장된다.
MB = 1024 * 1024
UUID_RE = re.compile(r"^[0-9A-Fa-f-]{36}$")    # 요청으로 들어오는 사진 ID 검증용
LOCAL_TZ = datetime.now().astimezone().tzinfo   # 촬영 시각을 이 Mac의 시간대로 표시

# ---------------------------------------------------------------------------
# 보관함 읽기
# ---------------------------------------------------------------------------

# 항목 목록을 읽는 쿼리. ZASSET은 사진과 동영상 한 건, ZADDITIONALASSETATTRIBUTES는
# 원본 크기와 원래 파일명을 담고 있다. 실제 보관함에서 확인한 값의 의미는 다음과 같다.
#   ZKIND: 0 사진, 1 동영상
#   ZKINDSUBTYPE: 10 스크린샷 (ZISDETECTEDSCREENSHOT도 함께 확인)
#   ZSAVEDASSETTYPE: 3, 6 본인 보관함 / 4 공유 앨범 항목
#   ZTRASHEDSTATE: 1 '최근 삭제된 항목'에 있는 항목
#   ZAVALANCHEUUID, ZAVALANCHEPICKTYPE: 버스트 묶음 ID와 선택 상태
QUERY = """
SELECT a.ZUUID, a.ZDATECREATED, a.ZKIND, a.ZKINDSUBTYPE, a.ZISDETECTEDSCREENSHOT,
       a.ZFAVORITE, a.ZHIDDEN, a.ZWIDTH, a.ZHEIGHT, a.ZAVALANCHEUUID, a.ZAVALANCHEPICKTYPE,
       b.ZORIGINALFILESIZE, b.ZORIGINALFILENAME, a.ZDIRECTORY, a.ZFILENAME, a.ZDURATION,
       a.ZSAVEDASSETTYPE, a.ZTRASHEDSTATE
FROM ZASSET a LEFT JOIN ZADDITIONALASSETATTRIBUTES b ON b.ZASSET = a.Z_PK
"""

# 버스트 선택 플래그(ZAVALANCHEPICKTYPE의 비트)
# 2는 대표로 고르지 않은 프레임, 4/8/16은 대표 프레임 또는 사용자가 고른 프레임이다.
BURST_NOT_SELECTED = 2
BURST_PICKED = 4 | 8 | 16


class Library:
    """사진 보관함 하나를 읽어 항목 목록을 메모리에 들고 있는 객체.

    items의 각 항목은 짧은 키를 쓰는 dict이다.
      u: 사진 ID(UUID)        t: 촬영 시각(유닉스 초)      d: 표시용 촬영 시각 문자열
      y: 촬영 연도            k: 종류(photo, video, shot)  fav: 즐겨찾기 여부
      hid: 가린 항목 여부     w, h: 가로, 세로 픽셀         av: 버스트 묶음 ID
      avp: 버스트 선택 플래그  s: 원본 크기(바이트)          n: 원래 파일명
      dur: 재생 시간(초)      lp: Mac에 있는 원본 경로       local: 원본이 Mac에 있는지
    """

    def __init__(self, path):
        self.path = path
        self.items = []
        self.by_uuid = {}
        self.error = None
        self.indexed_at = None
        self.shared_count = 0
        self.shared_bytes = 0
        self.lock = threading.Lock()

    @property
    def db_path(self):
        return os.path.join(self.path, "database", "Photos.sqlite")

    def _connect(self):
        # immutable=1: SQLite가 파일을 바꾸지 않는다고 가정하고 읽기만 한다(쓰기, 잠금 없음).
        uri = "file:" + quote(self.db_path) + "?mode=ro&immutable=1"
        return sqlite3.connect(uri, uri=True)

    def load(self):
        """보관함 목록을 읽어 메모리에 올린다. 읽기 전용.

        실패하면 self.error에 사용자에게 보여 줄 안내 문구를 남긴다.
        """
        if not os.path.isdir(self.path):
            self.error = (
                f"사진 보관함을 찾을 수 없습니다: {self.path}\n"
                "보관함 위치가 다르면 --library 옵션으로 지정하세요."
            )
            return
        rows = None
        last_err = None
        for _ in range(3):  # 사진 앱이 동시에 쓰는 중이면 드물게 실패하므로 재시도
            try:
                con = self._connect()
                rows = con.execute(QUERY).fetchall()
                con.close()
                break
            except PermissionError as e:
                last_err = e
                break
            except sqlite3.Error as e:
                last_err = e
                time.sleep(2)
        if rows is None:
            msg = str(last_err)
            if "unable to open" in msg or "authoriz" in msg or isinstance(last_err, PermissionError):
                self.error = (
                    "사진 보관함 데이터베이스를 열 수 없습니다. 권한 문제일 가능성이 큽니다.\n"
                    "시스템 설정 > 개인정보 보호 및 보안 > 전체 디스크 접근 권한에서 "
                    "'터미널'을 켠 뒤 프로그램을 다시 실행하세요.\n(원래 오류: " + msg + ")"
                )
            else:
                self.error = "보관함을 읽는 중 오류가 발생했습니다: " + msg
            return

        # 공유 앨범과 '최근 삭제된 항목'은 후보에서 빼고, 공유 앨범은 개수와 용량만 센다.
        items, shared_n, shared_b = [], 0, 0
        originals = os.path.join(self.path, "originals")
        for r in rows:
            (u, ts, kind, subtype, shot, fav, hidden, w, h, avu, avp,
             size, ofname, directory, fname, dur, saved, trashed) = r
            if not u or trashed:
                continue
            if saved == 4:  # 공유 앨범 항목(본인 보관함 용량과 무관)
                shared_n += 1
                shared_b += size or 0
                continue
            if saved not in (3, 6):
                continue
            t = (ts or 0) + APPLE_EPOCH
            dt = datetime.fromtimestamp(t, LOCAL_TZ)
            local_path = os.path.join(originals, directory or "", fname or "") if fname else ""
            items.append({
                "u": u,
                "t": t,
                "d": dt.strftime("%Y-%m-%d %H:%M:%S"),
                "y": dt.year,
                "k": "video" if kind == 1 else ("shot" if (shot == 1 or subtype == 10) else "photo"),
                "fav": bool(fav),
                "hid": bool(hidden),
                "w": w or 0,
                "h": h or 0,
                "av": avu or "",
                "avp": avp or 0,
                "s": size or 0,
                "n": ofname or fname or u,
                "dur": round(dur or 0),
                "lp": local_path,
                "local": bool(local_path) and os.path.exists(local_path),
            })
        # 새로고침 중에도 화면 요청이 들어올 수 있으므로 교체는 잠금 안에서 한 번에 한다.
        with self.lock:
            self.items = items
            self.by_uuid = {x["u"]: x for x in items}
            self.shared_count, self.shared_bytes = shared_n, shared_b
            self.indexed_at = datetime.now().strftime("%Y-%m-%d %H:%M")
            self.error = None

    # 썸네일과 미리보기 파일 찾기 -----------------------------------------------
    def _find(self, uuid, prefer_large):
        """사진 앱이 만들어 둔 미리보기 JPEG 경로를 찾는다. 없으면 None.

        resources/derivatives/masters/<첫 글자>/<UUID>_4_5005_c.jpeg 는 작은 썸네일,
        resources/derivatives/<첫 글자>/<UUID>_1_105_c.jpeg 는 큰 미리보기이다.
        원본이 iCloud에만 있어도 이 파일들은 대개 Mac에 있다.
        """
        res = os.path.join(self.path, "resources", "derivatives")
        c = uuid[0]
        small = [os.path.join(res, "masters", c, f"{uuid}_4_5005_c.jpeg")]
        large = [os.path.join(res, c, f"{uuid}_1_105_c.jpeg"),
                 os.path.join(res, c, f"{uuid}_1_102_o.jpeg")]
        order = large + small if prefer_large else small + large
        for p in order:
            if os.path.exists(p):
                return p
        # 그 밖의 이름 규칙
        for d in (os.path.join(res, "masters", c), os.path.join(res, c)):
            try:
                for f in os.listdir(d):
                    if f.startswith(uuid) and f.lower().endswith((".jpeg", ".jpg")):
                        return os.path.join(d, f)
            except OSError:
                pass
        return None

    def thumb(self, uuid):
        """격자 화면용 작은 이미지."""
        return self._find(uuid, prefer_large=False)

    def preview(self, uuid):
        """크게 보기용 큰 이미지."""
        return self._find(uuid, prefer_large=True)


# ---------------------------------------------------------------------------
# 필터
# ---------------------------------------------------------------------------

def public(x):
    """화면으로 보낼 필드만 남긴다. Mac 안의 파일 경로(lp)는 보내지 않는다."""
    return {k: x[k] for k in ("u", "d", "y", "k", "fav", "hid", "w", "h", "s", "n", "dur", "local")}


def base_filter(items, q):
    """모든 기준에 공통으로 쓰는 조건(즐겨찾기, 가린 항목, 촬영 기간)을 적용한다."""
    # 기간: YYYY-MM-DD 형식, 양 끝 날짜 포함
    d_from = q.get("date_from") or ""
    d_to = q.get("date_to") or ""
    excl_fav = q.get("exclude_fav", "1") == "1"
    excl_hid = q.get("exclude_hidden", "0") == "1"
    out = []
    for x in items:
        if excl_fav and x["fav"]:
            continue
        if excl_hid and x["hid"]:
            continue
        day = x["d"][:10]
        if d_from and day < d_from:
            continue
        if d_to and day > d_to:
            continue
        out.append(x)
    return out


def sort_items(items, sort):
    """new: 최신순, old: 오래된 순, 그 밖: 용량 큰 순."""
    if sort == "new":
        items.sort(key=lambda x: -x["t"])
    elif sort == "old":
        items.sort(key=lambda x: x["t"])
    else:
        items.sort(key=lambda x: -x["s"])
    return items


def flat_result(mode, res, q):
    """대용량, 스크린샷, 버스트 결과를 만든다.

    sort=group이면 비슷한 시간에 찍은 항목끼리 묶어 sections로 돌려준다.
    cluster는 묶는 간격(초)이며, 'day'이면 촬영 날짜가 같은 항목끼리 묶는다.
    그 밖의 정렬이면 items 목록 하나로 돌려준다.
    """
    sort = q.get("sort", "group")
    out = {"mode": mode, "count": len(res), "bytes": sum(x["s"] for x in res)}
    if sort != "group":
        out["items"] = [public(x) for x in sort_items(res, sort)]
        return out
    gap = q.get("cluster", "3600")
    by_time = sorted(res, key=lambda x: x["t"])
    sections, cur = [], []
    for x in by_time:
        if cur:
            same = (x["d"][:10] == cur[-1]["d"][:10]) if gap == "day" else (x["t"] - cur[-1]["t"] <= float(gap))
            if not same:
                sections.append(cur)
                cur = []
        cur.append(x)
    if cur:
        sections.append(cur)
    # 묶음은 합계 용량이 큰 순, 묶음 안은 촬영 시각 순
    sections.sort(key=lambda g: -sum(x["s"] for x in g))
    out["sections"] = [{"from": g[0]["d"], "to": g[-1]["d"], "bytes": sum(x["s"] for x in g),
                        "items": [public(x) for x in g]} for g in sections]
    return out


def run_query(lib, q):
    """화면의 조회 요청을 처리한다.

    mode
      large: 크기가 min_mb 이상인 항목(type으로 사진, 동영상 구분)
      screenshot: 스크린샷
      burst: 버스트에서 대표로 고르지 않은 프레임
      series: 촬영 간격이 gap초 이내로 이어진 사진 묶음. 묶음마다 1장을 남길 사진(keep)으로 정한다.
    """
    mode = q.get("mode", "large")
    sort = q.get("sort", "group")
    items = base_filter(lib.items, q)

    if mode == "large":
        min_b = float(q.get("min_mb", "100")) * MB
        typ = q.get("type", "all")
        res = [x for x in items if x["s"] >= min_b and (typ == "all" or x["k"] == typ)]
        return flat_result(mode, res, q)

    if mode == "screenshot":
        return flat_result(mode, [x for x in items if x["k"] == "shot"], q)

    if mode == "burst":
        # 사진 앱 화면에 보이지 않는 버스트 미선택 프레임
        res = [x for x in items if x["av"] and (x["avp"] & BURST_NOT_SELECTED)
               and not (x["avp"] & BURST_PICKED)]
        return flat_result(mode, res, q)

    if mode == "series":
        # 즐겨찾기는 묶음을 만들 때는 포함하고, 삭제 제안에서만 뺀다.
        protect_fav = q.get("exclude_fav", "1") == "1"
        items = base_filter(lib.items, dict(q, exclude_fav="0"))
        gap = float(q.get("gap", "1"))
        imgs = sorted((x for x in items if x["k"] == "photo" and not x["av"] and x["t"] > 0),
                      key=lambda x: x["t"])
        groups, cur = [], []
        for x in imgs:
            if cur and x["t"] - cur[-1]["t"] <= gap:
                cur.append(x)
            else:
                if len(cur) >= 2:
                    groups.append(cur)
                cur = [x]
        if len(cur) >= 2:
            groups.append(cur)
        # 남길 사진은 즐겨찾기, 해상도, 용량 순으로 고른다. 나머지가 삭제 제안이다.
        out, n, b = [], 0, 0
        for g in groups:
            keep = max(g, key=lambda x: (x["fav"], x["w"] * x["h"], x["s"]))
            extra = [x for x in g if x is not keep and not (protect_fav and x["fav"])]
            if not extra:
                continue
            n += len(extra)
            b += sum(x["s"] for x in extra)
            out.append({"keep": keep["u"], "d": g[0]["d"], "t": g[0]["t"],
                        "save": sum(x["s"] for x in extra),
                        "items": [public(x) for x in g]})
        if sort == "new":
            out.sort(key=lambda g: -g["t"])
        elif sort == "old":
            out.sort(key=lambda g: g["t"])
        else:
            out.sort(key=lambda g: -g["save"])
        for g in out:
            g.pop("t")
        return {"mode": mode, "groups": out, "count": n, "bytes": b, "group_count": len(out),
                "protect_fav": protect_fav}

    return {"error": "알 수 없는 모드"}


def summary(lib):
    """화면 상단에 보여 줄 보관함 요약."""
    if lib.error:
        return {"error": lib.error}
    items = lib.items
    years = sorted({x["y"] for x in items}, reverse=True)
    vids = [x for x in items if x["k"] == "video"]
    by_year = defaultdict(int)
    for x in vids:
        by_year[x["y"]] += x["s"]
    return {
        "library": lib.path,
        "indexed_at": lib.indexed_at,
        "count": len(items),
        "bytes": sum(x["s"] for x in items),
        "video_count": len(vids),
        "video_bytes": sum(x["s"] for x in vids),
        "shot_count": sum(1 for x in items if x["k"] == "shot"),
        "local_originals": sum(1 for x in items if x["local"]),
        "shared_count": lib.shared_count,
        "shared_bytes": lib.shared_bytes,
        "years": years,
        "first_date": min((x["d"][:10] for x in items if x["t"] > APPLE_EPOCH), default=""),
        "last_date": max((x["d"][:10] for x in items), default=""),
        "video_by_year": {str(k): v for k, v in sorted(by_year.items())},
    }


# ---------------------------------------------------------------------------
# 작업(앨범 만들기, 원본 내보내기) - 백그라운드 실행
# ---------------------------------------------------------------------------

# 진행 중이거나 끝난 작업의 상태. 화면이 /api/job/<id>로 1초마다 진행률을 확인한다.
JOBS = {}


def new_job(kind, total):
    """작업 상태를 새로 만들어 JOBS에 등록한다."""
    jid = uuidlib.uuid4().hex[:12]
    JOBS[jid] = {"id": jid, "kind": kind, "total": total, "done": 0,
                 "status": "running", "message": "", "errors": []}
    return JOBS[jid]


def as_str(s):
    """AppleScript 문자열 리터럴로 안전하게 변환."""
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def osascript(script, timeout=3600):
    """AppleScript를 실행하고 출력을 돌려준다. 실패하면 RuntimeError."""
    p = subprocess.run(["osascript", "-"], input=script, capture_output=True,
                       text=True, timeout=timeout)
    if p.returncode != 0:
        raise RuntimeError(p.stderr.strip() or "AppleScript 실행 실패")
    return p.stdout.strip()


def item_list_script(uuids):
    """사진 ID 목록을 사진 앱 항목 목록 L로 바꾸는 AppleScript 조각.

    사진 앱의 media item id는 'UUID/L0/001' 형식이다. 찾을 수 없는 항목은 건너뛴다.
    """
    ids = ", ".join(as_str(f"{u}/L0/001") for u in uuids)
    return f"""
    set L to {{}}
    repeat with i in {{{ids}}}
      try
        set m to media item id (contents of i)
        set chk to id of m
        set end of L to m
      end try
    end repeat"""


def job_album(job, name, uuids):
    """사진 앱에 새 앨범을 만들고 고른 항목을 200개씩 나눠 넣는다(백그라운드 스레드)."""
    try:
        album_id = osascript(
            f'tell application "Photos"\n'
            f'  set a to make new album named {as_str(name)}\n'
            f'  return id of a\nend tell')
        added = 0
        for i in range(0, len(uuids), 200):
            batch = uuids[i:i + 200]
            out = osascript(
                f'with timeout of 1800 seconds\n'
                f'tell application "Photos"\n'
                f'  set a to album id {as_str(album_id)}\n'
                f'{item_list_script(batch)}\n'
                f'  if (count of L) > 0 then add L to a\n'
                f'  return count of L\nend tell\nend timeout')
            added += int(out or 0)
            job["done"] = min(len(uuids), i + len(batch))
        job["status"] = "done"
        job["message"] = f"사진 앱에 '{name}' 앨범을 만들고 {added:,}개를 넣었습니다."
        if added < len(uuids):
            job["message"] += f" ({len(uuids) - added:,}개는 사진 앱에서 찾지 못했습니다.)"
    except Exception as e:  # noqa: BLE001
        job["status"] = "error"
        job["message"] = "앨범 만들기 실패: " + str(e)
        if "-1743" in str(e) or "not allowed" in str(e).lower():
            job["message"] += ("\n시스템 설정 > 개인정보 보호 및 보안 > 자동화에서 "
                               "'터미널'이 '사진'을 제어하도록 허용하세요.")


def unique_path(folder, name):
    """같은 이름이 있으면 _1, _2를 붙여 덮어쓰지 않는 경로를 만든다."""
    base, ext = os.path.splitext(name)
    p = os.path.join(folder, name)
    i = 1
    while os.path.exists(p):
        p = os.path.join(folder, f"{base}_{i}{ext}")
        i += 1
    return p


def job_export(job, lib, dest, uuids):
    """고른 항목의 원본을 dest로 복사한다(백그라운드 스레드).

    결과는 dest 안의 '내보내기_기록_날짜.csv'에 남긴다.
    """
    log_rows = []
    try:
        os.makedirs(dest, exist_ok=True)
        items = [lib.by_uuid[u] for u in uuids if u in lib.by_uuid]
        local = [x for x in items if x["local"]]
        remote = [x for x in items if not x["local"]]

        # 1) 맥에 원본이 있는 항목은 파일 복사(읽기만 함)
        for x in local:
            try:
                target = unique_path(dest, x["n"])
                shutil.copy2(x["lp"], target)
                try:
                    os.utime(target, (x["t"], x["t"]))
                except OSError:
                    pass
                log_rows.append([x["n"], x["d"], round(x["s"] / MB, 2), os.path.basename(target), "복사"])
            except OSError as e:
                job["errors"].append(str(e))
                log_rows.append([x["n"], x["d"], round(x["s"] / MB, 2), "", "실패"])
            job["done"] += 1

        # 2) 원본이 iCloud에만 있는 항목은 사진 앱에 '원본 내보내기'를 요청
        for i in range(0, len(remote), 10):
            batch = remote[i:i + 10]
            tmp = tempfile.mkdtemp(prefix=".export_", dir=dest)
            try:
                osascript(
                    'with timeout of 7200 seconds\n'
                    'tell application "Photos"\n'
                    f'{item_list_script([x["u"] for x in batch])}\n'
                    f'  if (count of L) > 0 then export L to (POSIX file {as_str(tmp)}) with using originals\n'
                    'end tell\nend timeout', timeout=7300)
                for f in sorted(os.listdir(tmp)):
                    target = unique_path(dest, f)
                    shutil.move(os.path.join(tmp, f), target)
                    log_rows.append([f, "", "", os.path.basename(target), "사진 앱 내보내기"])
            except Exception as e:  # noqa: BLE001
                job["errors"].append(str(e))
                for x in batch:
                    log_rows.append([x["n"], x["d"], round(x["s"] / MB, 2), "", "실패"])
            finally:
                shutil.rmtree(tmp, ignore_errors=True)
            job["done"] += len(batch)

        with open(os.path.join(dest, f"내보내기_기록_{datetime.now():%Y%m%d_%H%M%S}.csv"),
                  "w", newline="", encoding="utf-8-sig") as f:
            w = csv.writer(f)
            w.writerow(["원래 파일명", "촬영일시", "크기MB", "저장된 파일명", "방법"])
            w.writerows(log_rows)
        fails = sum(1 for r in log_rows if r[4] == "실패")
        job["status"] = "done" if not fails else "error"
        job["message"] = (f"{len(items) - fails:,}개 항목을 내보냈습니다: {dest}"
                          + (f" (실패 {fails:,}개, 기록 파일 참고)" if fails else ""))
    except Exception as e:  # noqa: BLE001
        job["status"] = "error"
        job["message"] = "내보내기 실패: " + str(e)


def choose_folder():
    """macOS 폴더 선택 창을 띄워 고른 폴더 경로를 돌려준다."""
    return osascript(
        'set f to choose folder with prompt "원본을 복사할 폴더(예: 외장 드라이브)를 고르세요"\n'
        'return POSIX path of f', timeout=600)


# ---------------------------------------------------------------------------
# 웹 서버
# ---------------------------------------------------------------------------

def make_handler(lib):
    """요청 처리기 클래스를 만든다.

    GET  /                 검토 화면(web/index.html)
    GET  /api/summary      보관함 요약
    GET  /api/query        기준별 후보 조회(count_only=1이면 개수와 용량만)
    GET  /api/job/<id>     작업 진행 상태
    GET  /thumb/<uuid>     작은 미리보기 이미지
    GET  /preview/<uuid>   큰 미리보기 이미지
    POST /api/refresh      보관함 다시 읽기
    POST /api/choose_folder  폴더 선택 창 열기
    POST /api/album        사진 앱에 앨범 만들기
    POST /api/export       원본 내보내기
    """
    class H(BaseHTTPRequestHandler):
        def log_message(self, *a):
            pass  # 터미널에 요청 기록을 찍지 않는다.

        def _send(self, code, body, ctype="application/json; charset=utf-8", cache=False):
            if isinstance(body, (dict, list)):
                body = json.dumps(body, ensure_ascii=False).encode()
            elif isinstance(body, str):
                body = body.encode()
            self.send_response(code)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "max-age=86400" if cache else "no-store")
            self.end_headers()
            self.wfile.write(body)

        def _file(self, path, ctype, cache=False):
            try:
                with open(path, "rb") as f:
                    self._send(200, f.read(), ctype, cache)
            except OSError:
                self._send(404, {"error": "not found"})

        def _body(self):
            n = int(self.headers.get("Content-Length") or 0)
            return json.loads(self.rfile.read(n) or b"{}")

        def do_GET(self):
            url = urlparse(self.path)
            q = {k: v[0] for k, v in parse_qs(url.query).items()}
            p = url.path
            if p in ("/", "/index.html"):
                return self._file(os.path.join(WEB_DIR, "index.html"), "text/html; charset=utf-8")
            if p == "/api/summary":
                return self._send(200, summary(lib))
            if p == "/api/query":
                if lib.error:
                    return self._send(200, {"error": lib.error})
                res = run_query(lib, q)
                if q.get("count_only") == "1":
                    res.pop("items", None)
                    res.pop("groups", None)
                    res.pop("sections", None)
                return self._send(200, res)
            if p.startswith("/api/job/"):
                return self._send(200, JOBS.get(p.rsplit("/", 1)[-1], {"error": "없는 작업"}))
            if p.startswith("/thumb/") or p.startswith("/preview/"):
                u = p.rsplit("/", 1)[-1]
                if not UUID_RE.match(u):
                    return self._send(400, {"error": "bad id"})
                f = lib.thumb(u) if p.startswith("/thumb/") else lib.preview(u)
                if not f:
                    return self._file(os.path.join(WEB_DIR, "noimage.svg"), "image/svg+xml", True)
                return self._file(f, "image/jpeg", cache=True)
            return self._send(404, {"error": "not found"})

        def do_POST(self):
            p = urlparse(self.path).path
            try:
                data = self._body()
            except ValueError:
                return self._send(400, {"error": "잘못된 요청"})
            if p == "/api/refresh":
                lib.load()
                return self._send(200, summary(lib))
            if p == "/api/choose_folder":
                try:
                    return self._send(200, {"path": choose_folder()})
                except Exception as e:  # noqa: BLE001
                    return self._send(200, {"error": "폴더 선택이 취소되었거나 실패했습니다. " + str(e)})
            # AppleScript에 넘기기 전에 ID 형식을 검사해 다른 문자열이 섞이지 않게 한다.
            uuids = [u for u in data.get("uuids", []) if isinstance(u, str) and UUID_RE.match(u)]
            if p == "/api/album":
                name = (data.get("name") or "").strip()[:100] or f"정리후보 {datetime.now():%Y-%m-%d}"
                if not uuids:
                    return self._send(400, {"error": "선택한 항목이 없습니다."})
                job = new_job("album", len(uuids))
                threading.Thread(target=job_album, args=(job, name, uuids), daemon=True).start()
                return self._send(200, job)
            if p == "/api/export":
                dest = data.get("dest") or ""
                if not uuids or not dest or not os.path.isabs(dest):
                    return self._send(400, {"error": "선택 항목 또는 폴더가 없습니다."})
                if os.path.realpath(dest).startswith(os.path.realpath(lib.path)):
                    return self._send(400, {"error": "사진 보관함 안으로는 내보낼 수 없습니다."})
                job = new_job("export", len(uuids))
                threading.Thread(target=job_export, args=(job, lib, dest, uuids), daemon=True).start()
                return self._send(200, job)
            return self._send(404, {"error": "not found"})

    return H


def main():
    """보관함을 읽고 웹 서버를 띄운 뒤 브라우저를 연다."""
    ap = argparse.ArgumentParser(description="사진 정리 도우미")
    ap.add_argument("--library", default=DEFAULT_LIBRARY, help="사진 보관함 경로")
    ap.add_argument("--port", type=int, default=8765)
    ap.add_argument("--no-browser", action="store_true")
    args = ap.parse_args()

    print("사진 정리 도우미")
    print("보관함을 읽는 중입니다. 잠시 기다려 주세요...")
    lib = Library(args.library)
    t0 = time.time()
    lib.load()
    if lib.error:
        print("\n[오류] " + lib.error + "\n")
    else:
        print(f"{len(lib.items):,}개 항목을 읽었습니다 ({time.time() - t0:.0f}초).")

    # 기본 포트가 사용 중이면 다음 번호를 차례로 시도한다. 외부 접속은 받지 않는다(127.0.0.1).
    server = None
    for port in range(args.port, args.port + 20):
        try:
            server = ThreadingHTTPServer(("127.0.0.1", port), make_handler(lib))
            break
        except OSError:
            continue
    if server is None:
        sys.exit("사용할 수 있는 포트를 찾지 못했습니다.")
    url = f"http://127.0.0.1:{server.server_address[1]}/"
    print(f"\n브라우저에서 {url} 을 엽니다.")
    print("프로그램을 끝내려면 이 창을 닫거나 Ctrl+C를 누르세요.\n")
    if not args.no_browser:
        threading.Timer(0.8, lambda: webbrowser.open(url)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\n종료합니다.")


if __name__ == "__main__":
    main()
