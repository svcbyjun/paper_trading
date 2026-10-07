#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
실시간 모의 주식 투자 프로그램 (PyQt5 + JSON/JSONL 파일 저장)

구조 (제안서 22~23장)
    UI (PyQt5)
      -> Application Layer (OrderService / PortfolioService / IdeaService)
      -> Simulation Engine (체결 / 잔고 검증 / 거래비용)
      -> Market Data Layer (MarketDataProvider 인터페이스 + 정규화된 Quote)
      -> 로컬 파일 저장소 (JSON / JSONL / CSV / LOG)

시장 데이터 제공자는 MarketDataProvider 만 구현하면 교체할 수 있다.
기본 제공자는 yfinance(Yahoo Finance, 무료·API 키 불필요, 1분봉)이다.
"""
from __future__ import annotations

import csv
import html
import json
import logging
import os
import re
import shutil
import sys
import uuid
import webbrowser
from abc import ABC, abstractmethod
from copy import deepcopy
from dataclasses import asdict, dataclass
from datetime import datetime, time as dtime, timedelta, timezone
from logging.handlers import RotatingFileHandler
from pathlib import Path
from typing import Optional
from urllib.parse import quote as urlquote
from zoneinfo import ZoneInfo

from PyQt5.QtCore import (QDate, QLockFile, QObject, QRunnable, Qt, QThreadPool,
                          QTimer, pyqtSignal)
from PyQt5.QtGui import QBrush, QColor
from PyQt5.QtWidgets import (QAbstractItemView, QApplication, QCheckBox, QComboBox,
                             QDateEdit, QDialog, QDialogButtonBox, QDoubleSpinBox,
                             QFileDialog, QFormLayout, QGridLayout, QGroupBox,
                             QHBoxLayout, QHeaderView, QInputDialog, QLabel,
                             QLineEdit, QMainWindow, QMessageBox, QPlainTextEdit,
                             QPushButton, QSpinBox, QSplitter, QTableWidget,
                             QTableWidgetItem, QTabWidget, QTextBrowser,
                             QVBoxLayout, QWidget)

# ============================================================================
# 상수 / 공통 유틸
# ============================================================================
APP_TITLE = "실시간 모의 주식 투자 프로그램"
BASE_DIR = Path(__file__).resolve().parent
POINTER_FILE = BASE_DIR / "data_location.txt"      # 데이터 저장 위치 변경 시 사용
BACKUP_ROOT = BASE_DIR / "backups"
SCHEMA_VERSION = 1
FOOTER_TEXT = "제작 : 제이유엔(svcbyjun@naver.com)"

MARKETS = ("KR", "US")
MARKET_LABEL = {"KR": "한국", "US": "미국"}
CURRENCY = {"KR": "KRW", "US": "USD"}
MONEY_DIGITS = {"KR": 0, "US": 2}

IDEA_STATUSES = ["작성", "관찰 중", "보유 중", "종료"]
IDEA_OUTCOMES = ["미분류", "성공", "실패"]

# 수수료/세금은 코드에 고정하지 않고 settings.json 의 값만 사용한다.
# 아래 값은 '처음 실행 시 채워지는 예시값'이므로 반드시 본인 증권사 기준으로 수정할 것.
DEFAULT_SETTINGS = {
    "version": SCHEMA_VERSION,
    "initial_cash": {"KR": 100_000_000, "US": 100_000},
    "fees": {
        "KR": {"buy_commission_pct": 0.015, "sell_commission_pct": 0.015,
               "sell_tax_pct": 0.18, "other_fee_fixed": 0},
        "US": {"buy_commission_pct": 0.25, "sell_commission_pct": 0.25,
               "sell_tax_pct": 0.00278, "other_fee_fixed": 0},
    },
    "market_data": {
        "provider": "yahoo",
        "api_key_env": "",            # API 키가 필요한 제공자용: 키를 담은 '환경 변수 이름'
        "refresh_seconds": 10,        # 호출 제한을 고려한 갱신 주기(초)
        "closed_refresh_seconds": 1800,
        "realtime_threshold_seconds": 150,   # 이 이내면 '실시간(1분봉)', 넘으면 '지연'
    },
    "trading": {"allow_orders_when_closed": False},
    "chart": {
        "url_templates": {
            "KR": "https://finance.yahoo.com/chart/{symbol}",
            "US": "https://finance.yahoo.com/chart/{symbol}",
        }
        # 사용 가능한 치환자: {symbol} {code} {tv_symbol}
        # 예) TradingView: https://www.tradingview.com/chart/?symbol={tv_symbol}
    },
    "backup": {"auto_backup": True, "interval_minutes": 30, "keep": 30},
}

# 한국 종목 빠른 검색용 기본 목록 (Yahoo 는 한글 종목명 검색이 약하므로 보완).
# data/custom_symbols.json 에 [{"market":"KR","name":"..","symbol":"123456.KS"}] 로 추가 가능.
KR_ALIASES = {
    "삼성전자": "005930.KS", "SK하이닉스": "000660.KS", "LG에너지솔루션": "373220.KS",
    "삼성바이오로직스": "207940.KS", "현대차": "005380.KS", "기아": "000270.KS",
    "셀트리온": "068270.KS", "KB금융": "105560.KS", "NAVER": "035420.KS",
    "카카오": "035720.KS", "POSCO홀딩스": "005490.KS", "삼성SDI": "006400.KS",
    "LG화학": "051910.KS", "에코프로": "086520.KQ", "에코프로비엠": "247540.KQ",
    "알테오젠": "196170.KQ", "HLB": "028300.KQ", "리가켐바이오": "141080.KQ",
    "펄어비스": "263750.KQ",
}

log = logging.getLogger("mocktrade")


def resolve_data_dir() -> Path:
    env = os.environ.get("MOCKTRADE_HOME")
    if env:
        return Path(env)
    try:
        if POINTER_FILE.exists():
            txt = POINTER_FILE.read_text(encoding="utf-8").strip()
            if txt:
                return Path(txt)
    except OSError:
        pass
    return BASE_DIR / "data"


def now_local() -> datetime:
    return datetime.now(timezone.utc).astimezone()


def now_iso() -> str:
    return now_local().isoformat(timespec="seconds")


def parse_iso(s: Optional[str]) -> Optional[datetime]:
    if not s:
        return None
    try:
        return datetime.fromisoformat(s)
    except ValueError:
        return None


def fmt_dt(s: Optional[str]) -> str:
    d = parse_iso(s)
    return d.astimezone().strftime("%Y-%m-%d %H:%M:%S") if d else "-"


def fmt_money(market: str, v: Optional[float]) -> str:
    if v is None:
        return "-"
    return f"{v:,.0f}원" if market == "KR" else f"${v:,.2f}"


def fmt_num(market: str, v: Optional[float]) -> str:
    if v is None:
        return "-"
    return f"{v:,.0f}" if market == "KR" else f"{v:,.2f}"


def fmt_pct(v: Optional[float]) -> str:
    return "-" if v is None else f"{v:+.2f}%"


def money_round(market: str, v: float) -> float:
    r = round(v, MONEY_DIGITS[market])
    return int(r) if MONEY_DIGITS[market] == 0 else r


def deep_merge(base: dict, over: dict) -> dict:
    out = deepcopy(base)
    for k, v in (over or {}).items():
        if isinstance(v, dict) and isinstance(out.get(k), dict):
            out[k] = deep_merge(out[k], v)
        else:
            out[k] = v
    return out


def setup_logging(log_dir: Path) -> None:
    log_dir.mkdir(parents=True, exist_ok=True)
    handler = RotatingFileHandler(log_dir / "app.log", maxBytes=1_000_000,
                                  backupCount=3, encoding="utf-8")
    handler.setFormatter(logging.Formatter("%(asctime)s [%(levelname)s] %(message)s"))
    root = logging.getLogger()
    root.handlers.clear()
    root.addHandler(handler)
    root.setLevel(logging.INFO)


# ============================================================================
# 파일 저장소 (JSON 원자적 쓰기 / JSONL append / 백업)
# ============================================================================
class StorageError(Exception):
    pass


def atomic_write_json(path: Path, data) -> None:
    """임시 파일에 먼저 쓰고 os.replace() 로 원자적 교체."""
    tmp = path.with_name(path.name + ".tmp")
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)
    except OSError as e:
        raise StorageError(f"파일 저장에 실패했습니다: {path}\n{e}") from e


def read_json(path: Path, default_factory):
    """파일이 없으면 기본값으로 생성. 파싱 실패 시 손상 파일을 보존하고 StorageError."""
    if not path.exists():
        data = default_factory()
        atomic_write_json(path, data)
        return data
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except json.JSONDecodeError as e:
        ts = now_local().strftime("%Y%m%d_%H%M%S")
        corrupt = path.with_name(f"{path.name}.corrupt-{ts}")
        try:
            shutil.copy2(path, corrupt)
        except OSError:
            pass
        raise StorageError(f"JSON 파싱에 실패했습니다: {path}\n"
                           f"(손상된 파일은 {corrupt.name} 로 보존했습니다. 백업에서 복원하세요.)\n{e}") from e
    except OSError as e:
        raise StorageError(f"파일을 읽을 수 없습니다: {path}\n{e}") from e


def append_jsonl(path: Path, record: dict) -> None:
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        with open(path, "a", encoding="utf-8") as f:
            f.write(json.dumps(record, ensure_ascii=False) + "\n")
            f.flush()
            os.fsync(f.fileno())
    except OSError as e:
        raise StorageError(f"거래 내역 저장에 실패했습니다: {path}\n{e}") from e


def read_jsonl(path: Path) -> list:
    rows = []
    if not path.exists():
        return rows
    try:
        with open(path, encoding="utf-8") as f:
            for n, line in enumerate(f, 1):
                line = line.strip()
                if not line:
                    continue
                try:
                    rows.append(json.loads(line))
                except json.JSONDecodeError:
                    log.error("JSONL 파싱 실패: %s (%d행) 건너뜀", path, n)
    except OSError as e:
        raise StorageError(f"파일을 읽을 수 없습니다: {path}\n{e}") from e
    return rows


class Repository:
    """data/ 아래 모든 파일의 읽기/쓰기를 담당."""

    def __init__(self, data_dir: Path):
        self.dir = Path(data_dir)
        self.settings: dict = {}
        self.accounts: dict = {}
        self.holdings: dict = {}
        self.ideas: dict = {}
        self.links: dict = {}
        self.performance: dict = {}
        self.custom_symbols: list = []
        self.needs_setup = False

    # ---- 경로 ----
    def p(self, *parts) -> Path:
        return self.dir.joinpath(*parts)

    @property
    def trades_path(self) -> Path:
        return self.p("trades", "trades.jsonl")

    # ---- 로딩 ----
    def load(self) -> None:
        self.dir.mkdir(parents=True, exist_ok=True)
        raw = read_json(self.p("settings.json"), lambda: deepcopy(DEFAULT_SETTINGS))
        self.settings = deep_merge(DEFAULT_SETTINGS, raw)
        self.needs_setup = any(not self.p("accounts", f"{m.lower()}.json").exists() for m in MARKETS)
        for m in MARKETS:
            ml = m.lower()
            if not self.needs_setup:
                self.accounts[m] = read_json(self.p("accounts", f"{ml}.json"), dict)
            self.holdings[m] = read_json(self.p("holdings", f"{ml}.json"),
                                         lambda m=m: {"version": SCHEMA_VERSION, "market": m, "positions": {}})
        self.ideas = read_json(self.p("ideas", "ideas.json"),
                               lambda: {"version": SCHEMA_VERSION, "ideas": []})
        self.links = read_json(self.p("ideas", "idea_trade_links.json"),
                               lambda: {"version": SCHEMA_VERSION, "links": []})
        self.performance = read_json(self.p("performance", "performance.json"),
                                     lambda: {"version": SCHEMA_VERSION, "updated_at": None})
        try:
            self.custom_symbols = read_json(self.p("custom_symbols.json"), list)
        except StorageError:
            self.custom_symbols = []
        self.trades_path.parent.mkdir(parents=True, exist_ok=True)
        self.trades_path.touch(exist_ok=True)

    def create_accounts(self, initial: dict) -> None:
        for m in MARKETS:
            acc = {"version": SCHEMA_VERSION, "market": m, "currency": CURRENCY[m],
                   "initial_cash": initial[m], "cash": initial[m],
                   "realized_pnl": 0, "created_at": now_iso()}
            self.accounts[m] = acc
            atomic_write_json(self.p("accounts", f"{m.lower()}.json"), acc)
        self.settings["initial_cash"] = dict(initial)
        self.save_settings()
        self.needs_setup = False

    # ---- 저장 ----
    def save_settings(self):
        atomic_write_json(self.p("settings.json"), self.settings)

    def save_account(self, m):
        atomic_write_json(self.p("accounts", f"{m.lower()}.json"), self.accounts[m])

    def save_holdings(self, m):
        atomic_write_json(self.p("holdings", f"{m.lower()}.json"), self.holdings[m])

    def save_ideas(self):
        atomic_write_json(self.p("ideas", "ideas.json"), self.ideas)

    def save_links(self):
        atomic_write_json(self.p("ideas", "idea_trade_links.json"), self.links)

    def save_performance(self):
        atomic_write_json(self.p("performance", "performance.json"), self.performance)

    def append_trade(self, trade: dict):
        append_jsonl(self.trades_path, trade)

    def read_trades(self) -> list:
        return read_jsonl(self.trades_path)

    # ---- 시세 캐시 ----
    def load_quote_cache(self) -> dict:
        try:
            raw = read_json(self.p("cache", "quotes.json"), lambda: {"version": SCHEMA_VERSION, "quotes": {}})
            return {s: Quote(**q) for s, q in raw.get("quotes", {}).items()}
        except (StorageError, TypeError) as e:
            log.warning("시세 캐시를 읽지 못했습니다: %s", e)
            return {}

    def save_quote_cache(self, quotes: dict):
        try:
            atomic_write_json(self.p("cache", "quotes.json"),
                              {"version": SCHEMA_VERSION,
                               "quotes": {s: asdict(q) for s, q in quotes.items()}})
        except StorageError as e:
            log.warning("%s", e)

    # ---- 초기화 ----
    def reset_all(self):
        for sub in ("accounts", "holdings", "trades", "ideas", "performance", "cache"):
            shutil.rmtree(self.p(sub), ignore_errors=True)
        self.accounts = {}
        self.load()


class BackupManager:
    EXCLUDE = {"logs", "cache", "app.lock"}

    def __init__(self, repo: Repository):
        self.repo = repo

    def create(self) -> Path:
        ts = now_local().strftime("%Y%m%d_%H%M%S")
        dest = BACKUP_ROOT / ts
        n = 1
        while dest.exists():
            dest = BACKUP_ROOT / f"{ts}_{n}"
            n += 1
        try:
            shutil.copytree(self.repo.dir, dest,
                            ignore=lambda d, names: [x for x in names if x in self.EXCLUDE
                                                     or x.endswith(".tmp")])
        except OSError as e:
            raise StorageError(f"백업에 실패했습니다: {e}") from e
        self._prune()
        return dest

    def list(self) -> list:
        if not BACKUP_ROOT.exists():
            return []
        return sorted([d for d in BACKUP_ROOT.iterdir() if d.is_dir()], reverse=True)

    def _prune(self):
        keep = int(self.repo.settings["backup"].get("keep", 30))
        for old in self.list()[keep:]:
            shutil.rmtree(old, ignore_errors=True)

    def restore(self, backup: Path):
        self.create()                       # 복원 전 현재 상태를 안전 백업
        try:
            for item in list(self.repo.dir.iterdir()):
                if item.name in self.EXCLUDE:
                    continue
                shutil.rmtree(item) if item.is_dir() else item.unlink()
            for item in backup.iterdir():
                dst = self.repo.dir / item.name
                shutil.copytree(item, dst) if item.is_dir() else shutil.copy2(item, dst)
        except OSError as e:
            raise StorageError(f"복원에 실패했습니다: {e}") from e


# ============================================================================
# 시장 운영 시간
# ============================================================================
class MarketClock:
    # (시간대, 개장, 폐장) - 공휴일은 반영하지 않는다(휴일에는 시세가 갱신되지 않아 '지연'으로 표시됨)
    SESSIONS = {"KR": ("Asia/Seoul", dtime(9, 0), dtime(15, 30)),
                "US": ("America/New_York", dtime(9, 30), dtime(16, 0))}

    @classmethod
    def is_open(cls, market: str, now: Optional[datetime] = None) -> bool:
        if market not in cls.SESSIONS:
            return False
        tz, o, c = cls.SESSIONS[market]
        now = (now or datetime.now(timezone.utc)).astimezone(ZoneInfo(tz))
        return now.weekday() < 5 and o <= now.time() < c

    @classmethod
    def label(cls, market: str) -> str:
        return "장중" if cls.is_open(market) else "휴장(장 마감/주말)"


# ============================================================================
# 시장 데이터 계층: 정규화된 모델 + 제공자 인터페이스
# ============================================================================
@dataclass
class SymbolInfo:
    market: str
    symbol: str       # 제공자 기준 심볼 (예: 005930.KS, AAPL)
    code: str         # 종목코드 / 티커
    name: str
    exchange: str = ""

    def label(self) -> str:
        ex = f" · {self.exchange}" if self.exchange else ""
        return f"{self.name} ({self.code}){ex}"

    @staticmethod
    def from_dict(d: dict) -> "SymbolInfo":
        return SymbolInfo(d["market"], d["symbol"], d.get("code", d["symbol"]),
                          d.get("name", d["symbol"]), d.get("exchange", ""))


@dataclass
class Quote:
    symbol: str
    market: str
    price: float
    open: float
    high: float
    low: float
    volume: int
    received_at: str                    # 데이터 수신 시각
    data_time: Optional[str] = None     # 시세 자체의 시각(제공자 기준)
    delay_seconds: Optional[float] = None
    source: str = ""

    def age_seconds(self) -> float:
        d = parse_iso(self.received_at)
        return (now_local() - d).total_seconds() if d else 1e9


def quote_status(q: Optional[Quote], threshold: float) -> tuple:
    """(표시 문구, 지연 여부) - 사용자가 최신가인지 지연가인지 알 수 있게 한다."""
    if q is None:
        return "시세 없음", True
    if not MarketClock.is_open(q.market):
        return f"휴장 · 마지막 가격 (시세 시각 {fmt_dt(q.data_time)})", False
    if q.delay_seconds is None:
        return "시세 시각 알 수 없음", True
    if q.delay_seconds <= threshold:
        return f"실시간(1분봉 기준) · 지연 {q.delay_seconds:.0f}초", False
    return f"⚠ 지연 시세 · 약 {q.delay_seconds / 60:.0f}분 지연", True


class MarketDataError(Exception):
    def __init__(self, msg: str, kind: str = "error"):
        super().__init__(msg)
        self.kind = kind     # network | rate_limit | not_found | auth | error


class MarketDataProvider(ABC):
    name = "base"

    @abstractmethod
    def search(self, query: str, market: str) -> list:
        """종목 검색 -> list[SymbolInfo]"""

    @abstractmethod
    def get_quote(self, info: SymbolInfo) -> Quote:
        """최신 시세 -> 정규화된 Quote"""


class YahooFinanceProvider(MarketDataProvider):
    """yfinance 기반. 무료/키 불필요. 한국 시세는 지연될 수 있으며 비공식 API이므로 호출 제한이 있다."""
    name = "yahoo"

    def __init__(self, custom_symbols: Optional[list] = None):
        self._yf = None
        self.custom = custom_symbols or []

    def _lib(self):
        if self._yf is None:
            try:
                import yfinance as yf
            except ImportError as e:
                raise MarketDataError("yfinance 가 설치되어 있지 않습니다. pip install yfinance", "error") from e
            self._yf = yf
        return self._yf

    @staticmethod
    def _wrap(e: Exception) -> MarketDataError:
        s = str(e).lower()
        if "too many requests" in s or "429" in s or "rate limit" in s:
            return MarketDataError("API 호출 제한을 초과했습니다. 잠시 후 다시 시도합니다.", "rate_limit")
        if any(k in s for k in ("connection", "timed out", "resolve", "network", "ssl", "unreachable")):
            return MarketDataError(f"API 연결에 실패했습니다: {e}", "network")
        if "401" in s or "403" in s or "unauthorized" in s:
            return MarketDataError(f"API 인증에 실패했습니다: {e}", "auth")
        return MarketDataError(f"시세 조회 오류: {e}", "error")

    def get_quote(self, info: SymbolInfo) -> Quote:
        yf = self._lib()
        try:
            t = yf.Ticker(info.symbol)
            df = t.history(period="1d", interval="1m")
            if df is None or df.empty:
                df = t.history(period="5d", interval="1m")
                if df is not None and not df.empty:
                    last_day = df.index[-1].date()
                    df = df[[d.date() == last_day for d in df.index]]
        except Exception as e:      # yfinance 는 다양한 예외를 던진다
            raise self._wrap(e) from e
        if df is None or df.empty:
            raise MarketDataError(f"시세 데이터를 받을 수 없습니다: {info.symbol}", "not_found")
        received = now_local()
        data_time = df.index[-1].to_pydatetime()
        if data_time.tzinfo is None:
            data_time = data_time.replace(tzinfo=timezone.utc)
        price = float(df["Close"].iloc[-1])
        if not price > 0:
            raise MarketDataError(f"유효하지 않은 가격입니다: {info.symbol}", "error")
        return Quote(
            symbol=info.symbol, market=info.market, price=price,
            open=float(df["Open"].iloc[0]), high=float(df["High"].max()),
            low=float(df["Low"].min()), volume=int(df["Volume"].sum()),
            received_at=received.isoformat(timespec="seconds"),
            data_time=data_time.astimezone().isoformat(timespec="seconds"),
            delay_seconds=max(0.0, (received - data_time).total_seconds()),
            source=self.name)

    # ---- 검색 ----
    def _exists(self, symbol: str) -> bool:
        try:
            df = self._lib().Ticker(symbol).history(period="5d", interval="1d")
            return df is not None and not df.empty
        except Exception:
            return False

    @staticmethod
    def _kr_info(symbol: str, name: str) -> SymbolInfo:
        code, suffix = symbol.split(".")
        return SymbolInfo("KR", symbol, code, name, "KOSPI" if suffix == "KS" else "KOSDAQ")

    def search(self, query: str, market: str) -> list:
        q = query.strip()
        if not q:
            return []
        out, seen = [], set()

        def add(info: SymbolInfo):
            if info.symbol not in seen:
                seen.add(info.symbol)
                out.append(info)

        # 1) 로컬 목록(기본 + 사용자 정의)
        if market == "KR":
            table = dict(KR_ALIASES)
            for c in self.custom:
                if c.get("market") == "KR" and c.get("symbol"):
                    table[c.get("name", c["symbol"])] = c["symbol"]
            for name, sym in table.items():
                if q.lower() in name.lower() or q.upper() == sym.split(".")[0]:
                    add(self._kr_info(sym, name))
        else:
            for c in self.custom:
                if c.get("market") == "US" and q.lower() in (c.get("name", "") + c.get("symbol", "")).lower():
                    add(SymbolInfo("US", c["symbol"], c["symbol"], c.get("name", c["symbol"]), c.get("exchange", "")))

        # 2) 제공자 검색
        names = {}
        try:
            res = self._lib().Search(q, max_results=10, news_count=0).quotes
        except MarketDataError:
            raise
        except Exception as e:
            err = self._wrap(e)
            if err.kind in ("network", "rate_limit", "auth"):
                raise err from e
            res = []
        found = []
        for r in res or []:
            sym = r.get("symbol", "")
            if r.get("quoteType") not in (None, "EQUITY", "ETF"):
                continue
            nm = r.get("shortname") or r.get("longname") or sym
            names[sym] = nm
            if market == "KR" and re.fullmatch(r"[0-9A-Za-z]{6}\.(KS|KQ)", sym):
                found.append(self._kr_info(sym, nm))
            elif market == "US" and "." not in sym and sym.isascii():
                found.append(SymbolInfo("US", sym, sym, nm, r.get("exchDisp") or r.get("exchange") or ""))

        # 3) 코드/티커 직접 입력 확인
        direct = []
        if market == "KR":
            m = re.fullmatch(r"([0-9A-Za-z]{6})(?:\.(KS|KQ))?", q)
            if m and not any(i.code == m.group(1).upper() for i in out):
                code = m.group(1).upper()
                for suf in ([m.group(2)] if m.group(2) else ["KS", "KQ"]):
                    sym = f"{code}.{suf}"
                    if self._exists(sym):
                        direct.append(self._kr_info(sym, names.get(sym, code)))
                        break
        elif re.fullmatch(r"[A-Za-z][A-Za-z\-]{0,9}", q):
            sym = q.upper()
            if sym not in seen and self._exists(sym):
                ex = next((f.exchange for f in found if f.symbol == sym), "")
                direct.append(SymbolInfo("US", sym, sym, names.get(sym, sym), ex))
        for i in direct + found:
            add(i)
        return out


PROVIDERS = {"yahoo": lambda repo: YahooFinanceProvider(repo.custom_symbols)}


def create_provider(repo: Repository) -> MarketDataProvider:
    """제공자 교체 지점. 새 API 는 MarketDataProvider 를 구현해 PROVIDERS 에 등록한다.
    API 키는 소스에 쓰지 않고 settings 의 api_key_env 가 가리키는 환경 변수에서 읽는다."""
    name = repo.settings["market_data"].get("provider", "yahoo")
    factory = PROVIDERS.get(name)
    if factory is None:
        raise MarketDataError(f"알 수 없는 시장 데이터 제공자: {name}", "error")
    return factory(repo)


def provider_api_key(repo: Repository) -> Optional[str]:
    env = repo.settings["market_data"].get("api_key_env", "")
    return os.environ.get(env) if env else None


# ---- 백그라운드 시세 갱신 ----
class _FetchSignals(QObject):
    done = pyqtSignal(dict, list)


class _FetchTask(QRunnable):
    def __init__(self, provider, infos, signals):
        super().__init__()
        self.provider, self.infos, self.signals = provider, infos, signals

    def run(self):
        out, errs = {}, []
        for info in self.infos:
            try:
                out[info.symbol] = self.provider.get_quote(info)
            except MarketDataError as e:
                errs.append((e.kind, f"{info.name}: {e}"))
                if e.kind in ("rate_limit", "auth", "network"):
                    break
            except Exception as e:
                log.exception("시세 조회 중 예기치 못한 오류")
                errs.append(("error", f"{info.name}: {e}"))
        self.signals.done.emit(out, errs)


class QuoteService(QObject):
    updated = pyqtSignal(dict)
    error = pyqtSignal(str, str)

    def __init__(self, repo: Repository, provider, store: dict):
        super().__init__()
        self.repo, self.provider, self.store = repo, provider, store
        self.watch: dict = {}
        self.force: set = set()
        self.busy = False
        self.pause_until: Optional[datetime] = None
        self.signals = _FetchSignals()
        self.signals.done.connect(self._on_done)
        self.timer = QTimer(self)
        self.timer.timeout.connect(self.tick)
        self.pool = QThreadPool.globalInstance()

    def start(self):
        self.timer.start(max(1, int(self.repo.settings["market_data"]["refresh_seconds"])) * 1000)
        QTimer.singleShot(200, self.tick)

    def set_watch(self, infos: list, force_symbols=()):
        self.watch = {i.symbol: i for i in infos}
        self.force.update(force_symbols)
        QTimer.singleShot(0, self.tick)

    def tick(self):
        if self.busy:
            return
        if self.pause_until and now_local() < self.pause_until:
            return
        md = self.repo.settings["market_data"]
        targets = []
        for sym, info in self.watch.items():
            q = self.store.get(sym)
            if sym in self.force or q is None:
                targets.append(info)
            elif MarketClock.is_open(info.market):
                targets.append(info)
            elif q.age_seconds() > md["closed_refresh_seconds"]:
                targets.append(info)          # 휴장 중에는 가끔만 갱신(마지막 가격 유지)
        if not targets:
            return
        self.force.clear()
        self.busy = True
        self.pool.start(_FetchTask(self.provider, targets, self.signals))

    def _on_done(self, quotes: dict, errs: list):
        self.busy = False
        if quotes:
            self.store.update(quotes)
            self.updated.emit(quotes)
        for kind, msg in errs:
            log.warning("시세 오류[%s] %s", kind, msg)
            if kind == "rate_limit":
                self.pause_until = now_local() + timedelta(seconds=60)
            self.error.emit(kind, msg)


# ============================================================================
# 시뮬레이션 엔진 (체결 / 잔고·수량 검증 / 거래비용)
# ============================================================================
class OrderError(Exception):
    pass


class FeeCalculator:
    def __init__(self, fees_cfg: dict):
        self.cfg = fees_cfg

    def calc(self, market: str, side: str, gross: float) -> tuple:
        c = self.cfg[market]
        pct = c["buy_commission_pct"] if side == "BUY" else c["sell_commission_pct"]
        commission = money_round(market, gross * pct / 100)
        tax = money_round(market, gross * c["sell_tax_pct"] / 100) if side == "SELL" else 0
        other = money_round(market, c.get("other_fee_fixed", 0))
        return commission, tax, other


class SimulationEngine:
    def __init__(self, repo: Repository):
        self.repo = repo

    def execute(self, info: SymbolInfo, quote: Quote, side: str, qty: int,
                idea_id: Optional[str] = None) -> dict:
        repo, m = self.repo, info.market
        if m not in MARKETS or m not in repo.accounts:
            raise OrderError("거래할 수 없는 시장입니다.")
        if quote is None or not quote.price > 0:
            raise OrderError("유효한 시세가 없어 주문할 수 없습니다.")
        if not isinstance(qty, int) or qty <= 0:
            raise OrderError("수량은 1주 이상의 정수여야 합니다.")
        if not MarketClock.is_open(m) and not repo.settings["trading"]["allow_orders_when_closed"]:
            raise OrderError(f"{MARKET_LABEL[m]} 시장은 현재 휴장 중입니다.\n"
                             "(설정 > '휴장 중에도 주문 허용'을 켜면 마지막 가격으로 테스트할 수 있습니다.)")
        acc = repo.accounts[m]
        positions = repo.holdings[m]["positions"]
        pos = positions.get(info.symbol)
        price = quote.price
        gross = money_round(m, price * qty)
        commission, tax, other = FeeCalculator(repo.settings["fees"]).calc(m, side, gross)
        fees = commission + tax + other
        realized = None

        if side == "BUY":
            total = money_round(m, gross + fees)
            if total > acc["cash"]:
                raise OrderError(f"잔고가 부족합니다. 현재 주문 가능 금액은 {fmt_money(m, acc['cash'])}입니다.")
            acc["cash"] = money_round(m, acc["cash"] - total)
            if pos is None:
                pos = {"symbol": info.symbol, "code": info.code, "name": info.name,
                       "market": m, "exchange": info.exchange, "quantity": 0,
                       "gross_cost": 0, "cost_basis": 0}
                positions[info.symbol] = pos
            pos["quantity"] += qty
            pos["gross_cost"] = money_round(m, pos["gross_cost"] + gross)
            pos["cost_basis"] = money_round(m, pos["cost_basis"] + total)
            net = total
        else:
            held = pos["quantity"] if pos else 0
            if held <= 0:
                raise OrderError("보유하지 않은 종목은 매도할 수 없습니다. (공매도 미지원)")
            if qty > held:
                raise OrderError(f"보유 수량이 부족합니다. 현재 보유 수량은 {held:,}주입니다.")
            proceeds = money_round(m, gross - fees)
            if qty == held:
                cost_removed, gross_removed = pos["cost_basis"], pos["gross_cost"]
            else:
                cost_removed = money_round(m, pos["cost_basis"] * qty / held)
                gross_removed = money_round(m, pos["gross_cost"] * qty / held)
            realized = money_round(m, proceeds - cost_removed)
            acc["cash"] = money_round(m, acc["cash"] + proceeds)
            acc["realized_pnl"] = money_round(m, acc["realized_pnl"] + realized)
            pos["quantity"] -= qty
            pos["cost_basis"] = money_round(m, pos["cost_basis"] - cost_removed)
            pos["gross_cost"] = money_round(m, pos["gross_cost"] - gross_removed)
            if pos["quantity"] == 0:
                del positions[info.symbol]
            net = proceeds

        trade = {
            "id": uuid.uuid4().hex[:12], "timestamp": now_iso(), "market": m,
            "currency": CURRENCY[m], "name": info.name, "symbol": info.symbol,
            "code": info.code, "side": side, "quantity": qty, "price": price,
            "gross_amount": gross, "commission": commission, "tax": tax, "other_fee": other,
            "net_amount": net, "cash_after": acc["cash"], "realized_pnl": realized,
            "idea_id": idea_id, "quote_received_at": quote.received_at,
            "quote_data_time": quote.data_time, "quote_delay_seconds": quote.delay_seconds,
        }
        # 저널(거래 내역) -> 보유 -> 계좌 순으로 기록
        repo.append_trade(trade)
        repo.save_holdings(m)
        repo.save_account(m)
        log.info("체결 %s %s %s x%d @ %s", m, side, info.symbol, qty, price)
        return trade


# ============================================================================
# 포트폴리오 / 투자 아이디어 서비스 (Application Layer)
# ============================================================================
class PortfolioService:
    def __init__(self, repo: Repository):
        self.repo = repo

    def positions(self, market: str, quotes: dict) -> list:
        rows = []
        for sym, p in self.repo.holdings[market]["positions"].items():
            q = quotes.get(sym)
            price = q.price if q else None
            mv = money_round(market, (price if price else p["gross_cost"] / p["quantity"]) * p["quantity"])
            pnl = money_round(market, mv - p["cost_basis"])
            rows.append({**p, "avg_price": p["gross_cost"] / p["quantity"], "price": price,
                         "market_value": mv, "pnl": pnl,
                         "pnl_pct": (pnl / p["cost_basis"] * 100) if p["cost_basis"] else None})
        return rows

    def summary(self, market: str, quotes: dict) -> dict:
        acc = self.repo.accounts[market]
        pos = self.positions(market, quotes)
        mv = sum(r["market_value"] for r in pos)
        cost = sum(r["cost_basis"] for r in pos)
        total = money_round(market, acc["cash"] + mv)
        unreal = money_round(market, mv - cost)
        init = acc["initial_cash"]
        return {"cash": acc["cash"], "market_value": mv, "total": total, "unrealized": unreal,
                "realized": acc["realized_pnl"], "return_pct": ((total - init) / init * 100) if init else None,
                "positions": pos}


class IdeaService:
    def __init__(self, repo: Repository):
        self.repo = repo

    @property
    def ideas(self) -> list:
        return self.repo.ideas["ideas"]

    def get(self, idea_id: Optional[str]) -> Optional[dict]:
        return next((i for i in self.ideas if i["id"] == idea_id), None)

    def links_of(self, idea_id: str) -> list:
        return [l for l in self.repo.links["links"] if l["idea_id"] == idea_id]

    def create(self, **f) -> dict:
        ts = now_iso()
        idea = {"id": uuid.uuid4().hex[:10], "created_at": ts, "updated_at": ts,
                "opened_at": None, "closed_at": None, "outcome": None,
                "post_review": {"auto": None, "sell_reason": "", "expected_vs_actual": "",
                                "evaluation": "", "reviewed_at": None}, **f}
        self.ideas.append(idea)
        self.repo.save_ideas()
        return idea

    def update(self, idea_id: str, **f):
        idea = self.get(idea_id)
        idea.update(f)
        idea["updated_at"] = now_iso()
        self.repo.save_ideas()

    def position(self, idea_id: str) -> dict:
        ls = self.links_of(idea_id)
        b = sum(l["quantity"] for l in ls if l["side"] == "BUY")
        s = sum(l["quantity"] for l in ls if l["side"] == "SELL")
        return {"bought": b, "sold": s, "open": b - s}

    def selectable_for(self, info: SymbolInfo, side: str) -> list:
        out = []
        for i in self.ideas:
            if i["symbol"] != info.symbol or i["status"] == "종료":
                continue
            if side == "SELL" and self.position(i["id"])["open"] <= 0:
                continue
            out.append(i)
        return out

    def validate_order(self, idea_id: Optional[str], info: SymbolInfo, side: str, qty: int):
        if not idea_id:
            return
        idea = self.get(idea_id)
        if idea is None:
            raise OrderError("선택한 투자 아이디어를 찾을 수 없습니다.")
        if idea["symbol"] != info.symbol:
            raise OrderError("투자 아이디어의 종목과 주문 종목이 다릅니다.")
        if idea["status"] == "종료":
            raise OrderError("이미 종료된 투자 아이디어에는 거래를 연결할 수 없습니다.")
        if side == "SELL":
            op = self.position(idea_id)["open"]
            if qty > op:
                raise OrderError(f"이 아이디어에 연결된 보유 수량은 {op:,}주입니다.\n"
                                 "연결 없이 매도하거나 수량을 줄여 주세요.")

    def metrics(self, idea: dict) -> Optional[dict]:
        ls = self.links_of(idea["id"])
        buys = [l for l in ls if l["side"] == "BUY"]
        sells = [l for l in ls if l["side"] == "SELL"]
        if not buys:
            return None
        bq = sum(l["quantity"] for l in buys)
        avg_buy = sum(l["price"] * l["quantity"] for l in buys) / bq
        buy_cost = sum(l["net_amount"] for l in buys)
        out = {"avg_buy_price": avg_buy, "buy_cost": buy_cost, "bought": bq,
               "first_buy_at": min(l["timestamp"] for l in buys),
               "expected_return_pct": None, "closed": False}
        tp = idea.get("target_price")
        if tp:
            out["expected_return_pct"] = (tp - avg_buy) / avg_buy * 100
        if sells:
            sq = sum(l["quantity"] for l in sells)
            proceeds = sum(l["net_amount"] for l in sells)
            avg_sell = sum(l["price"] * l["quantity"] for l in sells) / sq
            out.update({"sold": sq, "avg_sell_price": avg_sell, "proceeds": proceeds,
                        "last_sell_at": max(l["timestamp"] for l in sells)})
            if sq == bq:
                pnl = proceeds - buy_cost
                d0, d1 = parse_iso(out["first_buy_at"]), parse_iso(out["last_sell_at"])
                out.update({"closed": True, "realized_pnl": round(pnl, 2),
                            "actual_return_pct": pnl / buy_cost * 100 if buy_cost else None,
                            "holding_days": round((d1 - d0).total_seconds() / 86400, 1),
                            "target_reached": (avg_sell >= tp) if tp else None})
        return out

    def record_trade(self, idea_id: str, trade: dict) -> bool:
        """거래를 아이디어에 연결. 포지션이 모두 정리되면 아이디어를 종료하고 True 반환."""
        self.repo.links["links"].append({
            "idea_id": idea_id, "trade_id": trade["id"], "timestamp": trade["timestamp"],
            "side": trade["side"], "quantity": trade["quantity"], "price": trade["price"],
            "net_amount": trade["net_amount"]})
        self.repo.save_links()
        idea = self.get(idea_id)
        closed = False
        if trade["side"] == "BUY":
            idea["status"] = "보유 중"
            idea["opened_at"] = idea["opened_at"] or trade["timestamp"]
        else:
            if self.position(idea_id)["open"] == 0:
                idea["status"] = "종료"
                idea["closed_at"] = trade["timestamp"]
                m = self.metrics(idea)
                idea["post_review"]["auto"] = m
                if idea["outcome"] is None and m and m.get("realized_pnl") is not None:
                    idea["outcome"] = "성공" if m["realized_pnl"] > 0 else "실패"
                closed = True
        idea["updated_at"] = now_iso()
        self.repo.save_ideas()
        return closed

    def save_review(self, idea_id: str, outcome: str, sell_reason: str, eva: str, evaluation: str):
        idea = self.get(idea_id)
        idea["outcome"] = None if outcome == "미분류" else outcome
        idea["post_review"].update({"sell_reason": sell_reason, "expected_vs_actual": eva,
                                    "evaluation": evaluation, "reviewed_at": now_iso()})
        idea["updated_at"] = now_iso()
        self.repo.save_ideas()


class PerformanceService:
    def __init__(self, repo: Repository, ideas: IdeaService):
        self.repo, self.ideas = repo, ideas

    def update(self):
        done = [i for i in self.ideas.ideas if i["status"] == "종료" and i["outcome"] in ("성공", "실패")]
        rets = [i["post_review"]["auto"]["actual_return_pct"] for i in done
                if i["post_review"].get("auto") and i["post_review"]["auto"].get("actual_return_pct") is not None]
        tr = [i["post_review"]["auto"]["target_reached"] for i in done
              if i["post_review"].get("auto") and i["post_review"]["auto"].get("target_reached") is not None]
        self.repo.performance = {
            "version": SCHEMA_VERSION, "updated_at": now_iso(),
            "accounts": {m: {"initial_cash": a["initial_cash"], "cash": a["cash"],
                             "realized_pnl": a["realized_pnl"]} for m, a in self.repo.accounts.items()},
            "ideas": {"total": len(self.ideas.ideas), "closed": len(done),
                      "success": sum(1 for i in done if i["outcome"] == "성공"),
                      "failure": sum(1 for i in done if i["outcome"] == "실패"),
                      "avg_return_pct": (sum(rets) / len(rets)) if rets else None,
                      "target_reached_rate": (sum(1 for t in tr if t) / len(tr)) if tr else None}}
        try:
            self.repo.save_performance()
        except StorageError as e:
            log.warning("%s", e)


class OrderService:
    def __init__(self, engine: SimulationEngine, ideas: IdeaService, perf: PerformanceService):
        self.engine, self.ideas, self.perf = engine, ideas, perf

    def place_order(self, info: Optional[SymbolInfo], quote: Optional[Quote], side: str,
                    qty: int, idea_id: Optional[str] = None) -> tuple:
        if info is None:
            raise OrderError("존재하지 않는 종목입니다. 종목을 먼저 검색해 선택하세요.")
        self.ideas.validate_order(idea_id, info, side, qty)
        trade = self.engine.execute(info, quote, side, qty, idea_id)
        closed = False
        if idea_id:
            closed = self.ideas.record_trade(idea_id, trade)
        self.perf.update()
        return trade, closed


# ============================================================================
# 차트 (외부 플랫폼 연동)
# ============================================================================
def build_chart_url(settings: dict, info: SymbolInfo) -> str:
    tpl = settings["chart"]["url_templates"].get(info.market, "")
    tv = f"KRX:{info.code}" if info.market == "KR" else info.code
    try:
        return tpl.format(symbol=urlquote(info.symbol, safe=""), code=urlquote(info.code, safe=""),
                          tv_symbol=urlquote(tv, safe=":"))
    except (KeyError, IndexError, ValueError) as e:
        raise ValueError(f"차트 URL 템플릿이 올바르지 않습니다: {tpl}\n{e}") from e


# ============================================================================
# UI 공통
# ============================================================================
RED, BLUE = QColor("#d62728"), QColor("#1f5fbf")      # 한국식: 상승 빨강, 하락 파랑


def pnl_color(v: Optional[float]) -> Optional[QColor]:
    if v is None or v == 0:
        return None
    return RED if v > 0 else BLUE


def set_cell(table: QTableWidget, r: int, c: int, text, right=False, color: Optional[QColor] = None,
             data=None):
    it = QTableWidgetItem(str(text))
    it.setFlags(it.flags() & ~Qt.ItemIsEditable)
    if right:
        it.setTextAlignment(Qt.AlignRight | Qt.AlignVCenter)
    if color:
        it.setForeground(QBrush(color))
    if data is not None:
        it.setData(Qt.UserRole, data)
    table.setItem(r, c, it)


def make_table(headers: list) -> QTableWidget:
    t = QTableWidget(0, len(headers))
    t.setHorizontalHeaderLabels(headers)
    t.setSelectionBehavior(QAbstractItemView.SelectRows)
    t.setSelectionMode(QAbstractItemView.SingleSelection)
    t.setEditTriggers(QAbstractItemView.NoEditTriggers)
    t.horizontalHeader().setSectionResizeMode(QHeaderView.ResizeToContents)
    t.horizontalHeader().setStretchLastSection(True)
    t.verticalHeader().setVisible(False)
    t.setAlternatingRowColors(True)
    return t


def colored_label(text: str, color: Optional[QColor]) -> str:
    return f'<span style="color:{color.name()}">{html.escape(text)}</span>' if color else html.escape(text)


class SymbolPicker(QWidget):
    """시장 선택 + 종목 검색 + 결과 선택 (거래 화면 / 아이디어 대화상자 공용)"""
    changed = pyqtSignal(object)

    def __init__(self, win: "MainWindow"):
        super().__init__()
        self.win = win
        self.market = QComboBox()
        for m in MARKETS:
            self.market.addItem(MARKET_LABEL[m], m)
        self.query = QLineEdit()
        self.query.setPlaceholderText("종목명 / 종목코드 / 티커 (예: 삼성전자, 005930, AAPL)")
        self.btn = QPushButton("검색")
        self.results = QComboBox()
        self.results.setMinimumWidth(260)
        lay = QHBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        for w, s in ((self.market, 0), (self.query, 1), (self.btn, 0), (self.results, 1)):
            lay.addWidget(w, s)
        self.btn.clicked.connect(self.do_search)
        self.query.returnPressed.connect(self.do_search)
        self.results.currentIndexChanged.connect(lambda _: self.changed.emit(self.current()))

    def current(self) -> Optional[SymbolInfo]:
        d = self.results.currentData()
        return SymbolInfo.from_dict(d) if d else None

    def set_info(self, info: SymbolInfo):
        self.market.setCurrentIndex(MARKETS.index(info.market))
        self.results.blockSignals(True)
        self.results.clear()
        self.results.addItem(info.label(), asdict(info))
        self.results.blockSignals(False)
        self.changed.emit(info)

    def do_search(self):
        q = self.query.text().strip()
        if not q:
            QMessageBox.information(self, "종목 검색", "검색어를 입력하세요.")
            return
        QApplication.setOverrideCursor(Qt.WaitCursor)
        try:
            found = self.win.provider.search(q, self.market.currentData())
        except MarketDataError as e:
            QApplication.restoreOverrideCursor()
            QMessageBox.warning(self, "종목 검색 실패", str(e))
            return
        except Exception as e:
            QApplication.restoreOverrideCursor()
            log.exception("종목 검색 오류")
            QMessageBox.warning(self, "종목 검색 실패", f"검색 중 오류가 발생했습니다.\n{e}")
            return
        QApplication.restoreOverrideCursor()
        self.results.blockSignals(True)
        self.results.clear()
        for i in found:
            self.results.addItem(i.label(), asdict(i))
        self.results.blockSignals(False)
        if not found:
            QMessageBox.information(self, "종목 검색", f"'{q}' 에 해당하는 종목을 찾지 못했습니다.\n"
                                    "시장 선택(한국/미국)이 맞는지, 종목코드/티커가 정확한지 확인하세요.")
        self.changed.emit(self.current())


# ============================================================================
# 대화상자
# ============================================================================
class SetupDialog(QDialog):
    def __init__(self, defaults: dict, parent=None):
        super().__init__(parent)
        self.setWindowTitle("초기 자금 설정")
        form = QFormLayout(self)
        form.addRow(QLabel("처음 실행입니다. 시장별 가상 자금을 설정하세요.\n(한국/미국 계좌는 서로 독립적으로 관리됩니다.)"))
        self.kr, self.us = QDoubleSpinBox(), QDoubleSpinBox()
        for sp, m in ((self.kr, "KR"), (self.us, "US")):
            sp.setRange(1, 1e15)
            sp.setDecimals(MONEY_DIGITS[m])
            sp.setGroupSeparatorShown(True)
            sp.setValue(defaults[m])
        self.kr.setSuffix(" 원")
        self.us.setPrefix("$ ")
        form.addRow("한국 시장 초기 자금", self.kr)
        form.addRow("미국 시장 초기 자금", self.us)
        bb = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        bb.accepted.connect(self.accept)
        bb.rejected.connect(self.reject)
        form.addRow(bb)

    def values(self) -> dict:
        return {"KR": money_round("KR", self.kr.value()), "US": money_round("US", self.us.value())}


class IdeaDialog(QDialog):
    def __init__(self, win: "MainWindow", idea: Optional[dict] = None):
        super().__init__(win)
        self.win, self.idea = win, idea
        self.setWindowTitle("투자 아이디어 수정" if idea else "새 투자 아이디어")
        self.resize(640, 640)
        has_trades = bool(idea and win.ideas.links_of(idea["id"]))
        self.title = QLineEdit()
        self.picker = SymbolPicker(win)
        self.rationale = QPlainTextEdit()
        self.rationale.setPlaceholderText("왜 이 종목인가? 어떤 가격 움직임을 예상하는가?")
        self.entry = self._dspin()
        self.qty = QSpinBox()
        self.qty.setRange(0, 2_000_000_000)
        self.qty.setSpecialValueText("미입력")
        self.target = self._dspin()
        self.period = QLineEdit()
        self.period.setPlaceholderText("예: 6개월")
        self.status = QComboBox()
        self.status.addItems(["작성", "관찰 중", "종료"] if not has_trades else IDEA_STATUSES)
        self.memo = QPlainTextEdit()
        self.memo.setMaximumHeight(90)
        form = QFormLayout(self)
        form.addRow("아이디어 제목 *", self.title)
        form.addRow("종목 *", self.picker)
        form.addRow("투자 근거 *", self.rationale)
        form.addRow("매수 예정가", self.entry)
        form.addRow("매수 예정 수량", self.qty)
        form.addRow("목표가", self.target)
        form.addRow("예상 보유 기간", self.period)
        form.addRow("상태", self.status)
        form.addRow("추가 메모", self.memo)
        if has_trades:
            self.picker.setEnabled(False)
            self.status.setEnabled(False)
            form.addRow(QLabel("※ 연결된 거래가 있어 종목/상태는 변경할 수 없습니다. (상태는 거래에 따라 자동 변경)"))
        bb = QDialogButtonBox(QDialogButtonBox.Save | QDialogButtonBox.Cancel)
        bb.accepted.connect(self._save)
        bb.rejected.connect(self.reject)
        form.addRow(bb)
        if idea:
            self.title.setText(idea["title"])
            self.picker.set_info(SymbolInfo.from_dict(idea))
            self.rationale.setPlainText(idea["rationale"])
            self.entry.setValue(idea.get("planned_entry_price") or 0)
            self.qty.setValue(idea.get("planned_quantity") or 0)
            self.target.setValue(idea.get("target_price") or 0)
            self.period.setText(idea.get("expected_holding_period", ""))
            self.status.setCurrentText(idea["status"])
            self.memo.setPlainText(idea.get("memo", ""))

    @staticmethod
    def _dspin() -> QDoubleSpinBox:
        s = QDoubleSpinBox()
        s.setRange(0, 1e12)
        s.setDecimals(2)
        s.setGroupSeparatorShown(True)
        s.setSpecialValueText("미입력")
        return s

    def _save(self):
        info = self.picker.current()
        if not self.title.text().strip():
            return QMessageBox.warning(self, "입력 확인", "아이디어 제목을 입력하세요.")
        if info is None:
            return QMessageBox.warning(self, "입력 확인", "종목을 검색해서 선택하세요.")
        if not self.rationale.toPlainText().strip():
            return QMessageBox.warning(self, "입력 확인", "투자 근거를 입력하세요. 이 프로그램의 핵심 기록입니다.")
        f = {"title": self.title.text().strip(), "market": info.market, "name": info.name,
             "symbol": info.symbol, "code": info.code, "exchange": info.exchange,
             "rationale": self.rationale.toPlainText().strip(),
             "planned_entry_price": self.entry.value() or None,
             "planned_quantity": self.qty.value() or None,
             "target_price": self.target.value() or None,
             "expected_holding_period": self.period.text().strip(),
             "status": self.status.currentText(), "memo": self.memo.toPlainText().strip()}
        try:
            if self.idea:
                self.win.ideas.update(self.idea["id"], **f)
            else:
                self.win.ideas.create(**f)
        except StorageError as e:
            return QMessageBox.critical(self, "저장 실패", str(e))
        self.accept()


class ReviewDialog(QDialog):
    def __init__(self, win: "MainWindow", idea: dict):
        super().__init__(win)
        self.win, self.idea = win, idea
        self.setWindowTitle(f"사후 평가 - {idea['title']}")
        self.resize(620, 620)
        m = win.ideas.metrics(idea)
        mk = idea["market"]
        info = QTextBrowser()
        info.setMaximumHeight(170)
        info.setHtml(self._metrics_html(m, idea, mk))
        pr = idea["post_review"]
        self.outcome = QComboBox()
        self.outcome.addItems(IDEA_OUTCOMES)
        self.outcome.setCurrentText(idea["outcome"] or "미분류")
        self.reason = QPlainTextEdit(pr.get("sell_reason", ""))
        self.eva = QPlainTextEdit(pr.get("expected_vs_actual") or self._default_eva(m, idea, mk))
        self.evaluation = QPlainTextEdit(pr.get("evaluation", ""))
        form = QFormLayout(self)
        form.addRow(info)
        form.addRow("결과 분류", self.outcome)
        form.addRow("매도 이유", self.reason)
        form.addRow("예상과 실제 결과 비교", self.eva)
        form.addRow("사후 평가", self.evaluation)
        bb = QDialogButtonBox(QDialogButtonBox.Save | QDialogButtonBox.Cancel)
        bb.accepted.connect(self._save)
        bb.rejected.connect(self.reject)
        form.addRow(bb)

    @staticmethod
    def _metrics_html(m, idea, mk) -> str:
        if not m:
            return "연결된 거래가 없어 자동 집계값이 없습니다."
        rows = [("평균 매수가", fmt_num(mk, m["avg_buy_price"])),
                ("목표가", fmt_num(mk, idea.get("target_price")) if idea.get("target_price") else "-"),
                ("예상 수익률", fmt_pct(m["expected_return_pct"]))]
        if m.get("closed"):
            rows += [("실제 평균 매도가", fmt_num(mk, m["avg_sell_price"])),
                     ("실현손익(비용 반영)", fmt_money(mk, m["realized_pnl"])),
                     ("실제 수익률", fmt_pct(m["actual_return_pct"])),
                     ("보유 기간", f"{m['holding_days']}일"),
                     ("목표가 도달 여부", {True: "도달", False: "미도달", None: "-"}[m["target_reached"]])]
        else:
            rows.append(("상태", "아직 전량 매도되지 않음"))
        return "<table>" + "".join(f"<tr><td><b>{a}</b></td><td>&nbsp;&nbsp;{html.escape(b)}</td></tr>"
                                   for a, b in rows) + "</table>"

    @staticmethod
    def _default_eva(m, idea, mk) -> str:
        if not m or not m.get("closed"):
            return ""
        return (f"예상 목표가: {fmt_num(mk, idea.get('target_price')) if idea.get('target_price') else '-'}\n"
                f"실제 매도가: {fmt_num(mk, m['avg_sell_price'])}\n\n"
                f"예상 수익률: {fmt_pct(m['expected_return_pct'])}\n"
                f"실제 수익률: {fmt_pct(m['actual_return_pct'])}\n")

    def _save(self):
        try:
            self.win.ideas.save_review(self.idea["id"], self.outcome.currentText(),
                                       self.reason.toPlainText().strip(),
                                       self.eva.toPlainText().strip(),
                                       self.evaluation.toPlainText().strip())
            self.win.perf.update()
        except StorageError as e:
            return QMessageBox.critical(self, "저장 실패", str(e))
        self.accept()


# ============================================================================
# 탭: 대시보드
# ============================================================================
class DashboardTab(QWidget):
    FIELDS = [("cash", "현금 잔고"), ("market_value", "주식 평가금액"), ("total", "총 평가금액"),
              ("unrealized", "미실현손익(평가손익)"), ("realized", "실현손익"), ("return_pct", "누적 수익률")]

    def __init__(self, win: "MainWindow"):
        super().__init__()
        self.win = win
        lay = QVBoxLayout(self)
        top = QHBoxLayout()
        self.boxes = {}
        for m in MARKETS:
            gb = QGroupBox(f"{MARKET_LABEL[m]} 시장 ({CURRENCY[m]})")
            g = QGridLayout(gb)
            labels = {}
            state = QLabel()
            g.addWidget(state, 0, 0, 1, 2)
            for r, (k, t) in enumerate(self.FIELDS, 1):
                g.addWidget(QLabel(t), r, 0)
                labels[k] = QLabel("-")
                labels[k].setTextFormat(Qt.RichText)
                labels[k].setAlignment(Qt.AlignRight)
                g.addWidget(labels[k], r, 1)
            self.boxes[m] = (labels, state)
            top.addWidget(gb)
        lay.addLayout(top)
        lay.addWidget(QLabel("보유 종목"))
        self.table = make_table(["시장", "종목명", "코드", "수량", "평균 매수가", "현재가",
                                 "평가금액", "평가손익", "수익률", "시세 상태"])
        lay.addWidget(self.table, 1)

    def refresh(self):
        w = self.win
        rows = []
        thr = w.settings["market_data"]["realtime_threshold_seconds"]
        for m in MARKETS:
            labels, state = self.boxes[m]
            s = w.portfolio.summary(m, w.quotes)
            state.setText(f"시장 상태: <b>{MarketClock.label(m)}</b>")
            for k, _ in self.FIELDS:
                v = s[k]
                if k == "return_pct":
                    txt = colored_label(fmt_pct(v), pnl_color(v))
                elif k in ("unrealized", "realized"):
                    txt = colored_label(fmt_money(m, v), pnl_color(v))
                else:
                    txt = html.escape(fmt_money(m, v))
                labels[k].setText(f"<b>{txt}</b>")
            rows += [(m, r) for r in s["positions"]]
        self.table.setRowCount(len(rows))
        for i, (m, r) in enumerate(rows):
            st, delayed = quote_status(w.quotes.get(r["symbol"]), thr)
            c = pnl_color(r["pnl"])
            set_cell(self.table, i, 0, MARKET_LABEL[m])
            set_cell(self.table, i, 1, r["name"])
            set_cell(self.table, i, 2, r["code"])
            set_cell(self.table, i, 3, f"{r['quantity']:,}", True)
            set_cell(self.table, i, 4, fmt_num(m, r["avg_price"]), True)
            set_cell(self.table, i, 5, fmt_num(m, r["price"]), True)
            set_cell(self.table, i, 6, fmt_money(m, r["market_value"]), True)
            set_cell(self.table, i, 7, fmt_money(m, r["pnl"]), True, c)
            set_cell(self.table, i, 8, fmt_pct(r["pnl_pct"]), True, c)
            set_cell(self.table, i, 9, st, False, QColor("#b8860b") if delayed else None)


# ============================================================================
# 탭: 종목 검색 / 매매
# ============================================================================
class TradeTab(QWidget):
    def __init__(self, win: "MainWindow"):
        super().__init__()
        self.win = win
        self.info: Optional[SymbolInfo] = None
        lay = QVBoxLayout(self)
        self.picker = SymbolPicker(win)
        lay.addWidget(self.picker)
        gb = QGroupBox("시세")
        g = QGridLayout(gb)
        self.lbl = {}
        for i, (k, t) in enumerate([("name", "종목"), ("price", "현재가"), ("open", "시가"), ("high", "고가"),
                                    ("low", "저가"), ("volume", "거래량")]):
            g.addWidget(QLabel(t), i // 3, (i % 3) * 2)
            self.lbl[k] = QLabel("-")
            self.lbl[k].setStyleSheet("font-weight:bold")
            g.addWidget(self.lbl[k], i // 3, (i % 3) * 2 + 1)
        self.lbl["price"].setStyleSheet("font-weight:bold;font-size:18px")
        self.status = QLabel("-")
        self.rx = QLabel("-")
        g.addWidget(QLabel("데이터 상태"), 2, 0)
        g.addWidget(self.status, 2, 1, 1, 5)
        g.addWidget(QLabel("수신 시각"), 3, 0)
        g.addWidget(self.rx, 3, 1, 1, 5)
        lay.addWidget(gb)
        self.holding = QLabel("-")
        lay.addWidget(self.holding)
        row = QHBoxLayout()
        row.addWidget(QLabel("수량"))
        self.qty = QLineEdit()
        self.qty.setPlaceholderText("정수 (예: 100)")
        self.qty.setMaximumWidth(140)
        row.addWidget(self.qty)
        row.addWidget(QLabel("연결할 투자 아이디어"))
        self.idea = QComboBox()
        self.idea.setMinimumWidth(260)
        row.addWidget(self.idea, 1)
        lay.addLayout(row)
        btns = QHBoxLayout()
        self.buy = QPushButton("매수")
        self.sell = QPushButton("매도")
        self.chart = QPushButton("차트 보기")
        self.buy.setStyleSheet("background:#d62728;color:white;font-weight:bold;padding:8px 24px")
        self.sell.setStyleSheet("background:#1f5fbf;color:white;font-weight:bold;padding:8px 24px")
        for b in (self.buy, self.sell, self.chart):
            btns.addWidget(b)
        btns.addStretch(1)
        lay.addLayout(btns)
        lay.addStretch(1)
        self.picker.changed.connect(self.on_symbol)
        self.buy.clicked.connect(lambda: self.order("BUY"))
        self.sell.clicked.connect(lambda: self.order("SELL"))
        self.chart.clicked.connect(self.open_chart)
        self.populate_ideas()

    def on_symbol(self, info):
        self.info = info
        self.win.update_watch(force=[info.symbol] if info else [])
        self.populate_ideas()
        self.refresh()

    def populate_ideas(self):
        self.idea.clear()
        self.idea.addItem("(연결 안 함)", None)
        if self.info:
            for i in self.win.ideas.selectable_for(self.info, "BUY"):
                self.idea.addItem(f"[{i['status']}] {i['title']}", i["id"])

    def refresh(self):
        w, info = self.win, self.info
        if info is None:
            for k in self.lbl:
                self.lbl[k].setText("-")
            self.status.setText("종목을 검색해서 선택하세요.")
            self.rx.setText("-")
            self.holding.setText("-")
            return
        m = info.market
        q = w.quotes.get(info.symbol)
        self.lbl["name"].setText(info.label())
        if q:
            for k in ("price", "open", "high", "low"):
                self.lbl[k].setText(fmt_num(m, getattr(q, k)))
            self.lbl["volume"].setText(f"{q.volume:,}")
        else:
            for k in ("price", "open", "high", "low", "volume"):
                self.lbl[k].setText("-")
        txt, delayed = quote_status(q, w.settings["market_data"]["realtime_threshold_seconds"])
        self.status.setText(f"[{MarketClock.label(m)}] {txt}")
        self.status.setStyleSheet("color:#b8860b;font-weight:bold" if delayed else "color:#2e7d32;font-weight:bold")
        self.rx.setText(fmt_dt(q.received_at) if q else "-")
        pos = w.repo.holdings[m]["positions"].get(info.symbol)
        qty = pos["quantity"] if pos else 0
        avg = fmt_num(m, pos["gross_cost"] / qty) if pos else "-"
        self.holding.setText(f"보유 {qty:,}주 (평균 매수가 {avg}) · 주문 가능 현금 "
                             f"{fmt_money(m, w.repo.accounts[m]['cash'])}")

    def _parse_qty(self) -> Optional[int]:
        t = self.qty.text().strip().replace(",", "")
        if not t:
            QMessageBox.warning(self, "수량 확인", "수량을 입력하세요.")
        elif not re.fullmatch(r"\d+", t):
            QMessageBox.warning(self, "수량 확인", "수량은 0보다 큰 정수만 입력할 수 있습니다.\n"
                                "(음수, 소수, 문자는 사용할 수 없습니다.)")
        elif int(t) == 0:
            QMessageBox.warning(self, "수량 확인", "0주는 주문할 수 없습니다.")
        else:
            return int(t)
        return None

    def order(self, side: str):
        w, info = self.win, self.info
        if info is None:
            return QMessageBox.warning(self, "주문", "존재하지 않는 종목입니다. 종목을 먼저 검색해 선택하세요.")
        qty = self._parse_qty()
        if qty is None:
            return
        idea_id = self.idea.currentData()
        if side == "SELL":
            # 매도 시에는 해당 종목에 연결 가능한 아이디어를 별도로 묻는다
            cands = w.ideas.selectable_for(info, "SELL")
            if cands and idea_id is None:
                names = ["(연결 안 함)"] + [f"{c['title']}  (연결 보유 {w.ideas.position(c['id'])['open']:,}주)" for c in cands]
                pick, ok = QInputDialog.getItem(self, "투자 아이디어 연결", "이 매도를 연결할 아이디어:", names, 0, False)
                if not ok:
                    return
                idea_id = cands[names.index(pick) - 1]["id"] if names.index(pick) > 0 else None
        try:
            quote = w.get_fresh_quote(info)
            m = info.market
            gross = money_round(m, quote.price * qty)
            c, t, o = FeeCalculator(w.settings["fees"]).calc(m, side, gross)
            txt, delayed = quote_status(quote, w.settings["market_data"]["realtime_threshold_seconds"])
            msg = (f"{info.name} {qty:,}주 {'매수' if side == 'BUY' else '매도'} (시장가)\n\n"
                   f"체결 예정가: {fmt_num(m, quote.price)}\n거래금액: {fmt_money(m, gross)}\n"
                   f"수수료: {fmt_money(m, c)} / 세금: {fmt_money(m, t)} / 기타: {fmt_money(m, o)}\n"
                   f"{'차감' if side == 'BUY' else '입금'} 예정: "
                   f"{fmt_money(m, money_round(m, gross + c + t + o) if side == 'BUY' else money_round(m, gross - c - t - o))}\n\n"
                   f"시세 상태: {txt}")
            if QMessageBox.question(self, "주문 확인", msg) != QMessageBox.Yes:
                return
            trade, closed = w.orders.place_order(info, quote, side, qty, idea_id)
        except OrderError as e:
            return QMessageBox.warning(self, "주문 불가", str(e))
        except StorageError as e:
            log.exception("저장 실패")
            return QMessageBox.critical(self, "저장 실패", f"{e}\n\n프로그램 데이터가 일부만 저장되었을 수 있습니다. 백업 복원을 고려하세요.")
        self.qty.clear()
        w.update_watch()
        w.refresh_all()
        QMessageBox.information(self, "체결 완료",
                                f"{'매수' if side == 'BUY' else '매도'} 체결: {info.name} {qty:,}주 @ {fmt_num(info.market, trade['price'])}\n"
                                f"거래 후 현금: {fmt_money(info.market, trade['cash_after'])}")
        if closed:
            idea = w.ideas.get(idea_id)
            if QMessageBox.question(self, "투자 아이디어 종료",
                                    f"'{idea['title']}' 의 포지션이 모두 정리되어 종료되었습니다.\n지금 사후 평가를 작성할까요?") == QMessageBox.Yes:
                ReviewDialog(w, idea).exec_()
                w.refresh_all()

    def open_chart(self):
        if self.info is None:
            return QMessageBox.warning(self, "차트", "종목을 먼저 선택하세요.")
        self.win.open_chart(self.info)


# ============================================================================
# 탭: 투자 아이디어
# ============================================================================
class IdeasTab(QWidget):
    def __init__(self, win: "MainWindow"):
        super().__init__()
        self.win = win
        lay = QVBoxLayout(self)
        bar = QHBoxLayout()
        self.b_new = QPushButton("새 아이디어")
        self.b_edit = QPushButton("수정")
        self.b_review = QPushButton("사후 평가 작성/수정")
        self.b_trade = QPushButton("이 종목 매매하기")
        self.b_chart = QPushButton("차트 보기")
        for b in (self.b_new, self.b_edit, self.b_review, self.b_trade, self.b_chart):
            bar.addWidget(b)
        bar.addStretch(1)
        self.filter = QComboBox()
        self.filter.addItems(["전체", *IDEA_STATUSES])
        bar.addWidget(QLabel("상태 필터"))
        bar.addWidget(self.filter)
        lay.addLayout(bar)
        sp = QSplitter(Qt.Horizontal)
        self.table = make_table(["제목", "시장", "종목", "상태", "결과", "목표가", "작성일"])
        self.detail = QTextBrowser()
        sp.addWidget(self.table)
        sp.addWidget(self.detail)
        sp.setSizes([560, 520])
        lay.addWidget(sp, 1)
        self.b_new.clicked.connect(self.new)
        self.b_edit.clicked.connect(self.edit)
        self.b_review.clicked.connect(self.review)
        self.b_trade.clicked.connect(self.go_trade)
        self.b_chart.clicked.connect(self.chart)
        self.table.itemSelectionChanged.connect(self.show_detail)
        self.table.itemDoubleClicked.connect(lambda _: self.edit())
        self.filter.currentIndexChanged.connect(self.refresh)

    def selected(self) -> Optional[dict]:
        r = self.table.currentRow()
        if r < 0 or self.table.item(r, 0) is None:
            return None
        return self.win.ideas.get(self.table.item(r, 0).data(Qt.UserRole))

    def refresh(self):
        keep = (self.selected() or {}).get("id")
        flt = self.filter.currentText()
        items = [i for i in reversed(self.win.ideas.ideas) if flt == "전체" or i["status"] == flt]
        self.table.setRowCount(len(items))
        sel = -1
        for r, i in enumerate(items):
            m = i["market"]
            set_cell(self.table, r, 0, i["title"], data=i["id"])
            set_cell(self.table, r, 1, MARKET_LABEL[m])
            set_cell(self.table, r, 2, f"{i['name']} ({i['code']})")
            set_cell(self.table, r, 3, i["status"])
            set_cell(self.table, r, 4, i["outcome"] or "-",
                     color={"성공": RED, "실패": BLUE}.get(i["outcome"]))
            set_cell(self.table, r, 5, fmt_num(m, i["target_price"]) if i["target_price"] else "-", True)
            set_cell(self.table, r, 6, fmt_dt(i["created_at"])[:10])
            if i["id"] == keep:
                sel = r
        if sel >= 0:
            self.table.selectRow(sel)
        self.show_detail()

    def show_detail(self):
        i = self.selected()
        if not i:
            return self.detail.setHtml("<i>아이디어를 선택하세요.</i>")
        w, m = self.win, i["market"]
        esc = lambda s: html.escape(s or "").replace("\n", "<br>")
        pos = w.ideas.position(i["id"])
        met = w.ideas.metrics(i)
        q = w.quotes.get(i["symbol"])
        h = [f"<h3>{html.escape(i['title'])}</h3>",
             f"<p><b>{MARKET_LABEL[m]} · {html.escape(i['name'])} ({html.escape(i['code'])})</b><br>"
             f"상태: <b>{i['status']}</b> / 결과: <b>{i['outcome'] or '-'}</b></p>",
             f"<p><b>투자 근거</b><br>{esc(i['rationale'])}</p>",
             "<p>"
             f"매수 예정가: {fmt_num(m, i['planned_entry_price']) if i['planned_entry_price'] else '-'} / "
             f"예정 수량: {i['planned_quantity'] or '-'}<br>"
             f"목표가: {fmt_num(m, i['target_price']) if i['target_price'] else '-'} / "
             f"예상 보유 기간: {html.escape(i['expected_holding_period'] or '-')}</p>"]
        if i.get("memo"):
            h.append(f"<p><b>메모</b><br>{esc(i['memo'])}</p>")
        if met:
            h.append(f"<p><b>실제 진행</b><br>평균 매수가 {fmt_num(m, met['avg_buy_price'])} · 매수 {pos['bought']:,}주 · "
                     f"매도 {pos['sold']:,}주 · 보유 {pos['open']:,}주<br>첫 매수: {fmt_dt(met['first_buy_at'])}")
            if q and pos["open"] > 0:
                cur = (q.price - met["avg_buy_price"]) / met["avg_buy_price"] * 100
                h.append(f"<br>현재가 {fmt_num(m, q.price)} ({colored_label(fmt_pct(cur), pnl_color(cur))})")
            if met.get("closed"):
                h.append(f"<br>실현손익(비용 반영) {colored_label(fmt_money(m, met['realized_pnl']), pnl_color(met['realized_pnl']))} "
                         f"({fmt_pct(met['actual_return_pct'])}) · 보유 {met['holding_days']}일 · "
                         f"목표가 {({True: '도달', False: '미도달', None: '-'})[met['target_reached']]}")
            h.append("</p>")
        pr = i["post_review"]
        if pr.get("reviewed_at"):
            h.append(f"<hr><p><b>매도 이유</b><br>{esc(pr['sell_reason'])}</p>"
                     f"<p><b>예상 vs 실제</b><br>{esc(pr['expected_vs_actual'])}</p>"
                     f"<p><b>사후 평가</b><br>{esc(pr['evaluation'])}</p>")
        ls = w.ideas.links_of(i["id"])
        if ls:
            h.append("<hr><p><b>관련 거래</b></p><table cellpadding=3>")
            for l in ls:
                h.append(f"<tr><td>{fmt_dt(l['timestamp'])}</td><td>{'매수' if l['side'] == 'BUY' else '매도'}</td>"
                         f"<td align=right>{l['quantity']:,}주</td><td align=right>@ {fmt_num(m, l['price'])}</td></tr>")
            h.append("</table>")
        self.detail.setHtml("".join(h))

    def new(self):
        if IdeaDialog(self.win).exec_():
            self.win.refresh_all()

    def edit(self):
        i = self.selected()
        if not i:
            return QMessageBox.information(self, "투자 아이디어", "수정할 아이디어를 선택하세요.")
        if IdeaDialog(self.win, i).exec_():
            self.win.refresh_all()

    def review(self):
        i = self.selected()
        if not i:
            return QMessageBox.information(self, "투자 아이디어", "아이디어를 선택하세요.")
        if i["status"] != "종료":
            return QMessageBox.information(self, "사후 평가", "사후 평가는 '종료' 상태의 아이디어에 작성할 수 있습니다.\n"
                                           "(연결된 포지션을 모두 매도하면 자동으로 종료됩니다.)")
        if ReviewDialog(self.win, i).exec_():
            self.win.refresh_all()

    def go_trade(self):
        i = self.selected()
        if not i:
            return QMessageBox.information(self, "투자 아이디어", "아이디어를 선택하세요.")
        self.win.trade.picker.set_info(SymbolInfo.from_dict(i))
        k = self.win.trade.idea.findData(i["id"])
        if k >= 0:
            self.win.trade.idea.setCurrentIndex(k)
        self.win.tabs.setCurrentWidget(self.win.trade)

    def chart(self):
        i = self.selected()
        if i:
            self.win.open_chart(SymbolInfo.from_dict(i))


# ============================================================================
# 탭: 거래 내역
# ============================================================================
class HistoryTab(QWidget):
    HEAD = ["일시", "시장", "종목명", "코드", "구분", "수량", "체결가", "거래금액", "수수료",
            "세금", "기타비용", "정산금액", "거래 후 잔고", "투자 아이디어"]

    def __init__(self, win: "MainWindow"):
        super().__init__()
        self.win = win
        self.rows: list = []
        lay = QVBoxLayout(self)
        bar = QHBoxLayout()
        self.f_market = QComboBox()
        self.f_market.addItem("전체 시장", None)
        for m in MARKETS:
            self.f_market.addItem(MARKET_LABEL[m], m)
        self.f_symbol = QLineEdit()
        self.f_symbol.setPlaceholderText("종목명/코드")
        self.f_side = QComboBox()
        self.f_side.addItem("매수+매도", None)
        self.f_side.addItem("매수", "BUY")
        self.f_side.addItem("매도", "SELL")
        self.f_use = QCheckBox("기간")
        self.f_from, self.f_to = QDateEdit(), QDateEdit()
        for d in (self.f_from, self.f_to):
            d.setCalendarPopup(True)
            d.setDisplayFormat("yyyy-MM-dd")
        self.f_from.setDate(QDate.currentDate().addMonths(-1))
        self.f_to.setDate(QDate.currentDate())
        self.export = QPushButton("CSV 내보내기")
        for wd in (self.f_market, self.f_symbol, self.f_side, self.f_use, self.f_from, QLabel("~"), self.f_to):
            bar.addWidget(wd)
        bar.addStretch(1)
        bar.addWidget(self.export)
        lay.addLayout(bar)
        self.table = make_table(self.HEAD)
        lay.addWidget(self.table, 1)
        self.count = QLabel()
        lay.addWidget(self.count)
        for sig in (self.f_market.currentIndexChanged, self.f_side.currentIndexChanged,
                    self.f_symbol.textChanged, self.f_use.toggled, self.f_from.dateChanged, self.f_to.dateChanged):
            sig.connect(lambda *_: self.refresh())
        self.table.itemDoubleClicked.connect(self.detail)
        self.export.clicked.connect(self.export_csv)

    def refresh(self):
        try:
            trades = self.win.repo.read_trades()
        except StorageError as e:
            return QMessageBox.critical(self, "거래 내역", str(e))
        mk, sd, q = self.f_market.currentData(), self.f_side.currentData(), self.f_symbol.text().strip().lower()
        d0, d1 = self.f_from.date().toPyDate(), self.f_to.date().toPyDate()
        out = []
        for t in reversed(trades):
            if mk and t["market"] != mk or sd and t["side"] != sd:
                continue
            if q and q not in t["name"].lower() and q not in t["code"].lower():
                continue
            if self.f_use.isChecked():
                dt = parse_iso(t["timestamp"])
                if not dt or not (d0 <= dt.astimezone().date() <= d1):
                    continue
            out.append(t)
        self.rows = out
        self.table.setRowCount(len(out))
        for r, t in enumerate(out):
            m = t["market"]
            idea = self.win.ideas.get(t.get("idea_id"))
            vals = [fmt_dt(t["timestamp"]), MARKET_LABEL[m], t["name"], t["code"],
                    "매수" if t["side"] == "BUY" else "매도", f"{t['quantity']:,}", fmt_num(m, t["price"]),
                    fmt_num(m, t["gross_amount"]), fmt_num(m, t["commission"]), fmt_num(m, t["tax"]),
                    fmt_num(m, t["other_fee"]), fmt_num(m, t["net_amount"]), fmt_num(m, t["cash_after"]),
                    idea["title"] if idea else "-"]
            for c, v in enumerate(vals):
                set_cell(self.table, r, c, v, right=5 <= c <= 12,
                         color=(RED if t["side"] == "BUY" else BLUE) if c == 4 else None)
        self.count.setText(f"{len(out):,}건 표시 (전체 {len(trades):,}건)")

    def detail(self, item):
        t = self.rows[item.row()]
        idea = self.win.ideas.get(t.get("idea_id"))
        lines = [f"{k}: {v}" for k, v in t.items()]
        if idea:
            lines.append(f"연결된 아이디어 제목: {idea['title']}")
        d = QDialog(self)
        d.setWindowTitle("거래 상세")
        d.resize(480, 520)
        v = QVBoxLayout(d)
        tb = QPlainTextEdit("\n".join(lines))
        tb.setReadOnly(True)
        v.addWidget(tb)
        d.exec_()

    def export_csv(self):
        if not self.rows:
            return QMessageBox.information(self, "CSV 내보내기", "내보낼 거래가 없습니다.")
        path, _ = QFileDialog.getSaveFileName(self, "CSV 내보내기", "trades.csv", "CSV (*.csv)")
        if not path:
            return
        keys = list(self.rows[0].keys())
        try:
            with open(path, "w", encoding="utf-8-sig", newline="") as f:
                wr = csv.DictWriter(f, fieldnames=keys, extrasaction="ignore")
                wr.writeheader()
                wr.writerows(reversed(self.rows))
        except OSError as e:
            return QMessageBox.critical(self, "CSV 내보내기 실패", str(e))
        QMessageBox.information(self, "CSV 내보내기", f"{len(self.rows):,}건을 저장했습니다.\n{path}")


# ============================================================================
# 탭: 설정
# ============================================================================
class SettingsTab(QWidget):
    def __init__(self, win: "MainWindow"):
        super().__init__()
        self.win = win
        lay = QVBoxLayout(self)
        s = win.settings
        # 초기 자금 / 거래 비용
        self.cash, self.fee = {}, {}
        top = QHBoxLayout()
        for m in MARKETS:
            gb = QGroupBox(f"{MARKET_LABEL[m]} 시장")
            f = QFormLayout(gb)
            cash = QDoubleSpinBox()
            cash.setRange(0, 1e15)
            cash.setDecimals(MONEY_DIGITS[m])
            cash.setGroupSeparatorShown(True)
            cash.setValue(s["initial_cash"][m])
            cash.setEnabled(False)
            f.addRow("초기 자금 (변경은 '프로그램 초기화'에서)", cash)
            self.cash[m] = cash
            self.fee[m] = {}
            for key, label, dec in (("buy_commission_pct", "매수 수수료율 (%)", 5),
                                    ("sell_commission_pct", "매도 수수료율 (%)", 5),
                                    ("sell_tax_pct", "매도 세금률 (%)", 5),
                                    ("other_fee_fixed", f"기타 비용 (건당 고정, {CURRENCY[m]})", MONEY_DIGITS[m])):
                sp = QDoubleSpinBox()
                sp.setRange(0, 1e9 if key == "other_fee_fixed" else 100)
                sp.setDecimals(dec)
                sp.setSingleStep(0.001)
                sp.setValue(s["fees"][m][key])
                f.addRow(label, sp)
                self.fee[m][key] = sp
            top.addWidget(gb)
        lay.addLayout(top)
        lay.addWidget(QLabel("※ 수수료·세금 기본값은 예시입니다. 본인 증권사의 최신 수수료/세금 체계를 확인해 직접 수정하세요."))
        # 시장 데이터 / 차트 / 기타
        gb = QGroupBox("시장 데이터 · 차트 · 저장")
        f = QFormLayout(gb)
        self.provider = QComboBox()
        self.provider.addItems(list(PROVIDERS))
        self.provider.setCurrentText(s["market_data"]["provider"])
        self.api_env = QLineEdit(s["market_data"]["api_key_env"])
        self.api_env.setPlaceholderText("API 키가 필요한 제공자용: 키를 담은 환경 변수 이름 (키 자체는 입력 금지)")
        self.refresh = QSpinBox()
        self.refresh.setRange(1, 3600)
        self.refresh.setSuffix(" 초")
        self.refresh.setValue(s["market_data"]["refresh_seconds"])
        self.allow_closed = QCheckBox("휴장 중에도 주문 허용 (마지막 가격으로 테스트용)")
        self.allow_closed.setChecked(s["trading"]["allow_orders_when_closed"])
        self.chart_url = {}
        for m in MARKETS:
            e = QLineEdit(s["chart"]["url_templates"][m])
            e.setToolTip("치환자: {symbol} {code} {tv_symbol}\n예) https://www.tradingview.com/chart/?symbol={tv_symbol}")
            self.chart_url[m] = e
        self.data_dir = QLineEdit(str(win.repo.dir))
        self.data_dir.setReadOnly(True)
        pick = QPushButton("변경...")
        dd = QHBoxLayout()
        dd.addWidget(self.data_dir, 1)
        dd.addWidget(pick)
        self.auto_backup = QCheckBox("자동 백업")
        self.auto_backup.setChecked(s["backup"]["auto_backup"])
        self.backup_min = QSpinBox()
        self.backup_min.setRange(1, 1440)
        self.backup_min.setSuffix(" 분마다")
        self.backup_min.setValue(s["backup"]["interval_minutes"])
        bk = QHBoxLayout()
        bk.addWidget(self.auto_backup)
        bk.addWidget(self.backup_min)
        bk.addStretch(1)
        f.addRow("시장 데이터 제공자", self.provider)
        f.addRow("API 키 환경 변수명", self.api_env)
        f.addRow("시세 갱신 주기", self.refresh)
        f.addRow("주문", self.allow_closed)
        f.addRow("차트 URL (한국)", self.chart_url["KR"])
        f.addRow("차트 URL (미국)", self.chart_url["US"])
        f.addRow("데이터 저장 위치", dd)
        f.addRow("백업", bk)
        lay.addWidget(gb)
        row = QHBoxLayout()
        save = QPushButton("설정 저장")
        reset = QPushButton("프로그램 초기화...")
        reset.setStyleSheet("color:#b00020")
        row.addWidget(save)
        row.addStretch(1)
        row.addWidget(reset)
        lay.addLayout(row)
        lay.addStretch(1)
        save.clicked.connect(self.save)
        pick.clicked.connect(self.change_dir)
        reset.clicked.connect(self.reset)

    def save(self):
        w, s = self.win, self.win.settings
        for m in MARKETS:
            for k, sp in self.fee[m].items():
                s["fees"][m][k] = sp.value()
            s["chart"]["url_templates"][m] = self.chart_url[m].text().strip()
        s["market_data"].update({"provider": self.provider.currentText(),
                                 "api_key_env": self.api_env.text().strip(),
                                 "refresh_seconds": self.refresh.value()})
        s["trading"]["allow_orders_when_closed"] = self.allow_closed.isChecked()
        s["backup"].update({"auto_backup": self.auto_backup.isChecked(),
                            "interval_minutes": self.backup_min.value()})
        try:
            w.repo.save_settings()
            w.apply_settings()
        except (StorageError, MarketDataError) as e:
            return QMessageBox.critical(self, "설정 저장 실패", str(e))
        QMessageBox.information(self, "설정", "설정을 저장했습니다.")

    def change_dir(self):
        d = QFileDialog.getExistingDirectory(self, "데이터 저장 폴더 선택", str(self.win.repo.dir))
        if not d or Path(d).resolve() == self.win.repo.dir.resolve():
            return
        new = Path(d)
        if QMessageBox.question(self, "데이터 저장 위치", "현재 데이터를 새 폴더로 복사할까요?\n"
                                "(아니오를 누르면 새 폴더에서 빈 상태로 시작합니다.)") == QMessageBox.Yes:
            try:
                for item in self.win.repo.dir.iterdir():
                    if item.name in ("app.lock",):
                        continue
                    dst = new / item.name
                    shutil.copytree(item, dst, dirs_exist_ok=True) if item.is_dir() else shutil.copy2(item, dst)
            except OSError as e:
                return QMessageBox.critical(self, "복사 실패", str(e))
        try:
            POINTER_FILE.write_text(str(new), encoding="utf-8")
        except OSError as e:
            return QMessageBox.critical(self, "저장 실패", str(e))
        self.data_dir.setText(str(new))
        QMessageBox.information(self, "데이터 저장 위치", "프로그램을 재시작하면 새 위치가 적용됩니다.")

    def reset(self):
        w = self.win
        txt, ok = QInputDialog.getText(self, "프로그램 초기화",
                                       "계좌·보유·거래·투자 아이디어가 모두 삭제됩니다.\n(삭제 전 자동 백업됩니다)\n"
                                       "계속하려면 '초기화' 를 입력하세요.")
        if not ok or txt.strip() != "초기화":
            return
        try:
            w.backup.create()
            w.repo.reset_all()
        except StorageError as e:
            return QMessageBox.critical(self, "초기화 실패", str(e))
        w.ask_initial_funds(force=True)
        w.reload_state()


# ============================================================================
# 메인 윈도우
# ============================================================================
class MainWindow(QMainWindow):
    def __init__(self, repo: Repository):
        super().__init__()
        self.repo = repo
        self.backup = BackupManager(repo)
        self.quotes: dict = repo.load_quote_cache()
        self.provider = create_provider(repo)
        self.portfolio = PortfolioService(repo)
        self.ideas = IdeaService(repo)
        self.perf = PerformanceService(repo, self.ideas)
        self.orders = OrderService(SimulationEngine(repo), self.ideas, self.perf)
        self.setWindowTitle(APP_TITLE)
        self.resize(1180, 780)

        self.tabs = QTabWidget()
        self.dashboard = DashboardTab(self)
        self.trade = TradeTab(self)
        self.idea_tab = IdeasTab(self)
        self.history = HistoryTab(self)
        self.settings_tab = SettingsTab(self)
        for t, n in ((self.dashboard, "대시보드"), (self.trade, "종목 검색 / 매매"),
                     (self.idea_tab, "투자 아이디어"), (self.history, "거래 내역"), (self.settings_tab, "설정")):
            self.tabs.addTab(t, n)
        footer = QLabel(FOOTER_TEXT)
        footer.setAlignment(Qt.AlignCenter)
        footer.setStyleSheet("color:#777;padding:4px")
        central = QWidget()
        cl = QVBoxLayout(central)
        cl.setContentsMargins(0, 0, 0, 0)
        cl.addWidget(self.tabs, 1)
        cl.addWidget(footer)
        self.setCentralWidget(central)
        self.msg = QLabel("준비됨")
        self.statusBar().addPermanentWidget(self.msg)
        self._build_menu()

        self.svc = QuoteService(repo, self.provider, self.quotes)
        self.svc.updated.connect(self.on_quotes)
        self.svc.error.connect(self.on_quote_error)
        self._last_cache_save = now_local()
        self.ui_timer = QTimer(self)
        self.ui_timer.timeout.connect(self.refresh_quotes_ui)
        self.ui_timer.start(5000)
        self.backup_timer = QTimer(self)
        self.backup_timer.timeout.connect(self.auto_backup)
        self.apply_settings()
        self.update_watch()
        self.svc.start()
        self.refresh_all()

    @property
    def settings(self) -> dict:
        return self.repo.settings

    # ---- 메뉴 ----
    def _build_menu(self):
        mb = self.menuBar().addMenu("파일")
        for text, fn in (("지금 백업", self.manual_backup), ("백업에서 복원...", self.restore_backup),
                         ("데이터 폴더 열기", lambda: webbrowser.open(self.repo.dir.as_uri()))):
            a = mb.addAction(text)
            a.triggered.connect(fn)
        mb.addSeparator()
        mb.addAction("종료").triggered.connect(self.close)

    # ---- 설정 적용 ----
    def apply_settings(self):
        self.provider = create_provider(self.repo)
        if hasattr(self, "svc"):
            self.svc.provider = self.provider
            self.svc.timer.start(int(self.settings["market_data"]["refresh_seconds"]) * 1000)
        b = self.settings["backup"]
        self.backup_timer.stop()
        if b["auto_backup"]:
            self.backup_timer.start(int(b["interval_minutes"]) * 60_000)

    def ask_initial_funds(self, force=False):
        if not self.repo.needs_setup and not force:
            return
        dlg = SetupDialog(self.settings["initial_cash"], self)
        if not dlg.exec_():
            QMessageBox.information(self, "초기 자금", "초기 자금이 설정되지 않아 프로그램을 종료합니다.")
            sys.exit(0)
        self.repo.create_accounts(dlg.values())

    def reload_state(self):
        self.repo.load()
        self.quotes.clear()
        self.quotes.update(self.repo.load_quote_cache())
        for k, sp in self.settings_tab.cash.items():
            sp.setValue(self.settings["initial_cash"][k])
        self.trade.info = None
        self.update_watch()
        self.refresh_all()

    # ---- 시세 ----
    def update_watch(self, force=()):
        infos = {}
        for m in MARKETS:
            for p in self.repo.holdings[m]["positions"].values():
                infos[p["symbol"]] = SymbolInfo.from_dict(p)
        if self.trade.info:
            infos[self.trade.info.symbol] = self.trade.info
        self.svc.set_watch(list(infos.values()), force)

    def on_quotes(self, quotes: dict):
        self.refresh_quotes_ui()
        if (now_local() - self._last_cache_save).total_seconds() > 15:
            self.repo.save_quote_cache(self.quotes)
            self._last_cache_save = now_local()
        self.msg.setText(f"시세 갱신 {now_local().strftime('%H:%M:%S')}")

    def on_quote_error(self, kind: str, msg: str):
        label = {"rate_limit": "호출 제한", "network": "연결 실패", "auth": "인증 실패",
                 "not_found": "시세 없음"}.get(kind, "오류")
        self.msg.setText(f"⚠ {label}: {msg}")

    def refresh_quotes_ui(self):
        if not self.repo.accounts:
            return
        self.dashboard.refresh()
        self.trade.refresh()
        self.idea_tab.show_detail()

    def get_fresh_quote(self, info: SymbolInfo) -> Quote:
        """주문 직전 최신가를 직접 조회한다. 실패하면 30초 이내 캐시만 허용."""
        QApplication.setOverrideCursor(Qt.WaitCursor)
        try:
            q = self.provider.get_quote(info)
        except MarketDataError as e:
            cached = self.quotes.get(info.symbol)
            if cached and cached.age_seconds() <= 30:
                q = cached
            elif e.kind == "not_found":
                raise OrderError(f"존재하지 않거나 시세를 제공하지 않는 종목입니다: {info.name}") from e
            else:
                raise OrderError(f"최신 시세를 받지 못해 주문을 실행하지 않았습니다.\n{e}") from e
        finally:
            QApplication.restoreOverrideCursor()
        self.quotes[info.symbol] = q
        return q

    def open_chart(self, info: SymbolInfo):
        try:
            url = build_chart_url(self.settings, info)
        except ValueError as e:
            return QMessageBox.warning(self, "차트", str(e))
        if not webbrowser.open(url):
            QMessageBox.warning(self, "차트", f"기본 브라우저를 열지 못했습니다.\n{url}")

    # ---- 갱신 ----
    def refresh_all(self):
        if not self.repo.accounts:
            return
        self.trade.populate_ideas()
        self.dashboard.refresh()
        self.trade.refresh()
        self.idea_tab.refresh()
        self.history.refresh()

    # ---- 백업 ----
    def auto_backup(self):
        try:
            self.backup.create()
        except StorageError as e:
            log.warning("%s", e)
            self.msg.setText("⚠ 자동 백업 실패")

    def manual_backup(self):
        try:
            p = self.backup.create()
        except StorageError as e:
            return QMessageBox.critical(self, "백업 실패", str(e))
        QMessageBox.information(self, "백업", f"백업을 만들었습니다.\n{p}")

    def restore_backup(self):
        items = self.backup.list()
        if not items:
            return QMessageBox.information(self, "복원", "백업이 없습니다.")
        names = [d.name for d in items]
        pick, ok = QInputDialog.getItem(self, "백업에서 복원", "복원할 백업 (최신순):", names, 0, False)
        if not ok:
            return
        if QMessageBox.question(self, "복원", f"{pick} 시점으로 되돌립니다.\n현재 상태는 먼저 자동 백업됩니다. 계속할까요?") != QMessageBox.Yes:
            return
        try:
            self.backup.restore(items[names.index(pick)])
            self.reload_state()
        except StorageError as e:
            return QMessageBox.critical(self, "복원 실패", str(e))
        QMessageBox.information(self, "복원", "복원했습니다.")

    def closeEvent(self, e):
        try:
            self.repo.save_quote_cache(self.quotes)
            if self.settings["backup"]["auto_backup"]:
                self.backup.create()
        except StorageError as err:
            log.warning("%s", err)
        e.accept()


# ============================================================================
# 진입점
# ============================================================================
def install_excepthook():
    def hook(exc_type, exc, tb):
        log.error("처리되지 않은 예외", exc_info=(exc_type, exc, tb))
        if QApplication.instance():
            QMessageBox.critical(None, "오류", f"예기치 못한 오류가 발생했습니다.\n{exc}\n\n자세한 내용은 logs/app.log 를 확인하세요.")
    sys.excepthook = hook


def main() -> int:
    app = QApplication(sys.argv)
    app.setApplicationName("MockTrade")
    data_dir = resolve_data_dir()
    try:
        data_dir.mkdir(parents=True, exist_ok=True)
        setup_logging(data_dir / "logs")
    except OSError as e:
        QMessageBox.critical(None, "시작 실패", f"데이터 폴더를 사용할 수 없습니다.\n{data_dir}\n{e}")
        return 1
    install_excepthook()

    lock = QLockFile(str(data_dir / "app.lock"))
    if not lock.tryLock(200):
        QMessageBox.warning(None, "이미 실행 중", "프로그램이 이미 실행 중입니다.\n같은 데이터를 동시에 사용할 수 없습니다.")
        return 1

    repo = Repository(data_dir)
    try:
        repo.load()
    except StorageError as e:
        log.error("%s", e)
        bm = BackupManager(repo)
        backups = bm.list()
        msg = f"{e}\n\n"
        if backups and QMessageBox.question(None, "데이터 오류",
                                            msg + f"가장 최근 백업({backups[0].name})으로 복원할까요?") == QMessageBox.Yes:
            try:
                bm.restore(backups[0])
                repo = Repository(data_dir)
                repo.load()
            except StorageError as e2:
                QMessageBox.critical(None, "복원 실패", str(e2))
                return 1
        else:
            if not backups:
                QMessageBox.critical(None, "데이터 오류", msg + "사용할 수 있는 백업이 없습니다.")
            return 1

    if repo.needs_setup:
        dlg = SetupDialog(repo.settings["initial_cash"])
        if not dlg.exec_():
            return 0
        try:
            repo.create_accounts(dlg.values())
        except StorageError as e:
            QMessageBox.critical(None, "저장 실패", str(e))
            return 1

    try:
        win = MainWindow(repo)
    except MarketDataError as e:
        QMessageBox.critical(None, "시장 데이터 설정 오류", str(e))
        return 1
    win.show()
    code = app.exec_()
    lock.unlock()
    return code


if __name__ == "__main__":
    sys.exit(main())