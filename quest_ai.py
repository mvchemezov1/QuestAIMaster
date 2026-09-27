#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Text Quest AI — Российская версия (без генерации изображений).

Провайдеры текста:
  * GigaChat (Сбер)  — бесплатный тариф Freemium
  * YandexGPT        — стартовый грант при регистрации
  * OpenRouter       — доступ к GPT/Claude/Llama и др. через один ключ
  * DeepSeek         — дешёвый и быстрый OpenAI-совместимый API
  * Ollama           — локальный сервер для полностью офлайн-игры
  * Custom           — любой свой OpenAI-совместимый эндпоинт

Возможности:
  * ИИ-гейммастер ведёт повествование по заданной истории.
  * Голосовой ввод (SpeechRecognition) и озвучка (pyttsx3) — опционально.
  * Автоматические карточки предметов/существ с экспортом в Markdown/JSON.
  * Инвентарь и экипировка по слотам тела, учёт в промпте ИИ.
  * Кнопки действий: авто от ИИ + свои собственные.
  * Мультиплеер по сети (хост + клиенты).
  * Экономия запросов: пул ключей с автопереключением и батчинг ходов.
"""

import os
import re
import math
import json
import time
import glob
import random
import queue
import socket
import threading
import traceback
import importlib.util
import urllib.request
import urllib.error
import webbrowser
import tkinter as tk
from functools import partial

# --- Опциональный keyring (безопасное хранение ключей) ---
try:
    import keyring as _keyring_mod
    _KEYRING_ENABLED = True
except Exception:
    _keyring_mod = None
    _KEYRING_ENABLED = False
from tkinter import ttk, messagebox, filedialog, simpledialog
from dataclasses import dataclass, field, asdict, fields
from datetime import datetime

APP_DIR = os.path.join(os.path.expanduser("~"), ".quest_ai")
os.makedirs(APP_DIR, exist_ok=True)
PRESETS_FILE = os.path.join(APP_DIR, "story_presets.json")
SETTINGS_FILE = os.path.join(APP_DIR, "app_settings.json")

# --- Плагины ---
MODS_DIR = os.path.join(APP_DIR, "mods")
os.makedirs(MODS_DIR, exist_ok=True)
MODS_README = os.path.join(MODS_DIR, "README.md")
PLUGIN_PROVIDER_KIND = "plugin"

# --- Безопасность и надёжность ---
KEYRING_SERVICE = "quest_ai"
KEYRING_POOL_KEY = "text_key_pool"

# Максимум символов в одной строке сетевого протокола. Защищает от
# бесконечных «линий» со стороны злонамеренного или сломанного пира.
MAX_LINE_CHARS = 1024 * 1024      # 1M символов

# Idle-таймаут: если клиент только шлёт ping, но ни разу за N миллисекунд
# не отправил ни действие, ни сообщение чата, ни своё состояние — отключаем.
IDLE_TIMEOUT_MS = 5 * 60 * 1000   # 5 минут

# Ограничения для JSON, приходящего извне (карточки, квесты).
MAX_JSON_BYTES = 64 * 1024        # 64 КБ на одну сущность
MAX_JSON_DEPTH = 8                # уровень вложенности

# Ограничения на строки в карточках.
MAX_CARD_NAME_LEN = 200
MAX_CARD_DESC_LEN = 4000
MAX_CARD_PROP_VALUE_LEN = 500
MAX_CARD_PROPS_COUNT = 50

# --- Сохранения игры ---
SAVES_DIR = os.path.join(APP_DIR, "saves")
os.makedirs(SAVES_DIR, exist_ok=True)
AUTOSAVE_FILE = os.path.join(SAVES_DIR, "autosave.json")

SAVE_VERSION = 1
AUTOSAVE_EVERY_N_TURNS = 5   # автосейв каждые N ходов
RECENT_SAVES_COUNT = 5       # сколько показывать в подменю
UNDO_STACK_LIMIT = 20        # глубина истории откатов в ходах

# --- Расширенные карточки ---
CARD_STATUSES = ["жив", "мёртв", "потерян", "уничтожен", "неизвестно"]
CARD_ATTITUDES = ["союзник", "нейтрал", "враг", "неизвестно"]

# --- Журнал квестов ---
QUEST_STATUSES = ["active", "done", "failed"]
QUEST_STATUS_LABELS = {
    "active": "активен",
    "done": "выполнен",
    "failed": "провален",
}
QUEST_STATUS_ALIASES = {
    "active": "active", "активен": "active", "активный": "active",
    "в процессе": "active", "открыт": "active", "текущий": "active",
    "done": "done", "выполнен": "done", "завершён": "done",
    "завершен": "done", "готово": "done", "completed": "done",
    "failed": "failed", "провален": "failed", "провалено": "failed",
    "провал": "failed", "провалился": "failed",
}

# --- RPG-механика ---
DEFAULT_STATS = {
    "сила": 10,
    "ловкость": 10,
    "интеллект": 10,
    "харизма": 10,
    "здоровье": 20,
    "мана": 5,
}
STAT_NAMES = list(DEFAULT_STATS.keys())

ROLL_RE = re.compile(r"\[ROLL](.*?)\[/ROLL]", re.DOTALL | re.IGNORECASE)
AUTO_ROLL_CHAIN_LIMIT = 3   # макс. последовательных бросков без хода игрока
# --- Локации и карта мира ---
LOCATION_RE = re.compile(r"\[LOCATION](.*?)\[/LOCATION]", re.DOTALL | re.IGNORECASE)

# ---------------------------------------------------------------------------
# Провайдеры текста
# ---------------------------------------------------------------------------

TEXT_PROVIDERS = {
    "gigachat": {
        "label": "GigaChat (Сбер) — бесплатный тариф Freemium",
        "model": "GigaChat-2",
        "signup_url": "https://developers.sber.ru/studio",
        "kind": "gigachat",
    },
    "yandexgpt": {
        "label": "YandexGPT — стартовый грант при регистрации",
        "model": "yandexgpt-lite",
        "signup_url": "https://yandex.cloud/ru/docs/ai-studio/",
        "kind": "yandex",
    },
    "openrouter": {
        "label": "OpenRouter — GPT/Claude/Llama через один ключ",
        "model": "openai/gpt-4o-mini",
        "signup_url": "https://openrouter.ai/keys",
        "kind": "openai",
        "base_url": "https://openrouter.ai/api/v1",
        "extra_headers": {
            "HTTP-Referer": "https://github.com/text-quest-ai",
            "X-Title": "Text Quest AI",
        },
    },
    "deepseek": {
        "label": "DeepSeek — дешёвый и быстрый",
        "model": "deepseek-chat",
        "signup_url": "https://platform.deepseek.com/api_keys",
        "kind": "openai",
        "base_url": "https://api.deepseek.com/v1",
    },
    "ollama": {
        "label": "Ollama — локальный сервер (офлайн, без ключа)",
        "model": "llama3.1",
        "signup_url": "https://ollama.com/download",
        "kind": "openai",
        "base_url": "http://localhost:11434/v1",
        "no_key": True,
    },
    "custom": {
        "label": "Свой OpenAI-совместимый сервер",
        "model": "",
        "signup_url": "",
        "kind": "openai",
        "base_url": "",
        "no_key": True,
    },
}

# Слоты экипировки
EQUIPMENT_SLOTS = [
    ("head",    "Голова"),
    ("amulet",  "Шея"),
    ("body",    "Тело"),
    ("hands",   "Руки"),
    ("legs",    "Ноги"),
    ("feet",    "Обувь"),
    ("belt",    "Пояс"),
    ("weapon",  "Оружие (правая рука)"),
    ("shield",  "Левая рука / щит"),
    ("ring",    "Кольцо"),
]
EQUIPMENT_SLOT_IDS = {sid for sid, _ in EQUIPMENT_SLOTS}
EQUIPMENT_SLOT_LABELS = dict(EQUIPMENT_SLOTS)

ACTIONS_RE = re.compile(r"\[ACTIONS](.*?)\[/ACTIONS]", re.DOTALL | re.IGNORECASE)
CARD_RE = re.compile(r"\[CARD](.*?)\[/CARD]", re.DOTALL | re.IGNORECASE)
QUEST_RE = re.compile(r"\[QUEST](.*?)\[/QUEST]", re.DOTALL | re.IGNORECASE)

HISTORY_KEEP_RECENT = 10
HISTORY_COMPRESS_TRIGGER = 20

DEFAULT_MP_PORT = 5050
ACTION_BATCH_WINDOW_MS = 2500

# --- Логи и статистика ---
LOGS_DIR = os.path.join(APP_DIR, "logs")
os.makedirs(LOGS_DIR, exist_ok=True)
ERROR_LOG_FILE = os.path.join(LOGS_DIR, "errors.log")
ERROR_LOG_MAX_BYTES = 2 * 1024 * 1024  # 2 МБ — после этого ротация в .old
LOG_PROMPT_HEAD = 1500                  # сколько символов промпта писать в лог
LOG_RESPONSE_HEAD = 1500                # сколько символов ответа/ошибки писать

# Приблизительные цены за 1M токенов (валюта, цена input, цена output).
# Уточняйте на страницах провайдеров — тарифы меняются.
PROVIDER_PRICING = {
    "gigachat":   ("₽", 0.0, 0.0),      # Freemium
    "yandexgpt":  ("₽", 200.0, 200.0),  # условно
    "openrouter": ("$", 0.15, 0.60),    # ~gpt-4o-mini
    "deepseek":   ("$", 0.14, 0.28),
    "ollama":     ("—", 0.0, 0.0),      # локально
    "custom":     ("—", 0.0, 0.0),
}

# --- Голос ---
TTS_MAX_CHUNK = 240        # символов в одном «куске» для pyttsx3
TTS_RATE_DEFAULT = 180     # стандартная скорость, слов в минуту
STT_LANGUAGE = "ru-RU"

# --- Мультиплеер v2 ---
HEARTBEAT_INTERVAL_MS = 15000   # клиент шлёт ping каждые 15 с
HEARTBEAT_TIMEOUT_MS = 45000    # если pong не пришёл за 45 с — переподключение
RECONNECT_BASE_DELAY_MS = 1000  # первая задержка переподключения
RECONNECT_MAX_DELAY_MS = 30000  # максимальная задержка между попытками
RECONNECT_MAX_ATTEMPTS = 12     # после этого — сдаёмся и выходим в оффлайн

ROLE_HOST = "host"
ROLE_PLAYER = "player"
ROLE_OBSERVER = "observer"
ROLE_LABELS = {
    ROLE_HOST: "ведущий",
    ROLE_PLAYER: "игрок",
    ROLE_OBSERVER: "наблюдатель",
}

# --- Стилевые пресеты ---
STYLE_PRESETS = {
    "Мрачное фэнтези": (
        "мрачно, атмосферно, с элементами хоррора и отчаяния; "
        "серые моральные выборы, мир суров и несправедлив; "
        "не бойся описывать грязь, холод, голод и усталость"
    ),
    "Героическое фэнтези": (
        "эпично и возвышенно; герои — образцы доблести; "
        "битвы описаны кинематографично, без лишнего натурализма; "
        "акцент на подвигах, товариществе и судьбе"
    ),
    "Юмор и пародия": (
        "с иронией, шутками и абсурдом; герои попадают в нелепые "
        "ситуации и выкручиваются с блеском; не бойся ломать "
        "четвёртую стену, играть с клише и подмигивать читателю"
    ),
    "Нуар": (
        "короткие рубленые фразы, дождь, сигаретный дым и неон; "
        "герой — уставший одиночка с тёмным прошлым; "
        "все лгут, истина стоит дорого"
    ),
    "Лавкрафтианский ужас": (
        "медленно нарастающее ощущение неправильности; "
        "древние силы за гранью человеческого понимания; "
        "безумие и отчаяние ближе, чем победа; "
        "натурализм ужаса важнее экшена"
    ),
    "Уютное приключение": (
        "тёплое, неспешное, с юмором и заботой о деталях быта; "
        "мир враждебен, но не жесток; главное — relationships и "
        "маленькие радости, а не эпические битвы"
    ),
}

MODERATION_MODES = {
    "none": "",
    "soft": (
        "\nМОДЕРАЦИЯ КОНТЕНТА: без явного натурализма. "
        "Не описывай подробно расчленёнку, кровь, потроха, тошноту, "
        "пытки; не изображай секс напрямую (упоминание и намёк — можно). "
        "Насилие и эротика могут присутствовать в сюжете, но за кадром "
        "или вскользь.\n"
    ),
    "strict": (
        "\nМОДЕРАЦИЯ КОНТЕНТА (жёсткая): без насилия и эротики. "
        "Не описывай кровь, смерть в подробностях, физическое страдание, "
        "сексуальный контент любого рода. Конфликты разрешаются "
        "нелетально: драка → «ты уклоняешься и противник падает», "
        "угроза → «климат накаляется», романтика → «между вами "
        "пробегает искра». Сохраняй сюжет, но сглаживай опасные сцены.\n"
    ),
}

DEFAULT_AI_TEMPERATURE = 0.7
DEFAULT_AI_MAX_TOKENS = 1500
DEFAULT_AI_TOP_P = 0.95
REGEN_TEMPERATURE_DELTA = 0.2

# --- UX ---
INPUT_HISTORY_LIMIT = 50
TYPING_TICK_MS = 400

# Палитры для светлой и тёмной темы.
THEMES = {
    "light": {
        "bg":          "#F0F0F0",
        "fg":          "#111111",
        "story_bg":    "#FFFFFF",
        "story_fg":    "#111111",
        "story_sel":   "#BBDEFB",
        "status_fg":   "#666666",
        "stats_fg":    "#888888",
        "chat_bg":     "#FFFFFF",
        "chat_fg":     "#111111",
        "canvas_bg":   "#F7F7F7",
        "tree_bg":     "#FFFFFF",
        "tree_fg":     "#111111",
    },
    "dark": {
        "bg":          "#232323",
        "fg":          "#E6E6E6",
        "story_bg":    "#161616",
        "story_fg":    "#E6E6E6",
        "story_sel":   "#3D5A80",
        "status_fg":   "#9A9A9A",
        "stats_fg":    "#7C7C7C",
        "chat_bg":     "#1A1A1A",
        "chat_fg":     "#D0D0D0",
        "canvas_bg":   "#151515",
        "tree_bg":     "#1A1A1A",
        "tree_fg":     "#D0D0D0",
    },
}

# Регулярка для разметки **bold**, *italic*, `code`.
MD_PATTERN = re.compile(r"(\*\*[^*\n]+\*\*|\*[^*\n]+\*|`[^`\n]+`)")

# --- Профили генерации ---
GENERATION_PROFILES = {
    "Точно / Канон": {"temperature": 0.3, "top_p": 0.85},
    "Сбалансированно": {"temperature": 0.7, "top_p": 0.95},
    "Творчески":     {"temperature": 1.0, "top_p": 0.98},
}

# --- Длина хода ---
TURN_LENGTHS = {
    "short": "короткие (2-4 предложения на ход)",
    "medium": "средние (4-8 предложений на ход)",
    "long": "длинные (8-14 предложений, подробные описания)",
}
DEFAULT_TURN_LENGTH = "medium"


def build_system_prompt(cfg, summary: str = "", multiplayer: bool = False,
                        player_state=None, other_players=None,
                        quest_store=None, location_store=None,
                        current_location: str = "",
                        card_store=None,
                        important_facts: list = None,
                        turn_length: str = DEFAULT_TURN_LENGTH,
                        plugin_prompt_hooks: list = None,
                        plugin_context: dict = None) -> str:
    summary_block = ""
    if summary:
        summary_block = (
            "\nКРАТКОЕ СОДЕРЖАНИЕ ПРЕДЫДУЩИХ СОБЫТИЙ (память сюжета — учитывай "
            "при продолжении истории, но не пересказывай его читателю заново):\n"
            f"{summary}\n"
        )
    multiplayer_block = ""
    if multiplayer:
        multiplayer_block = (
            "\nВ этой партии одновременно участвует НЕСКОЛЬКО игроков. В одном "
            "ходу тебе может прийти сразу несколько действий — каждое начинается "
            "с имени игрока перед двоеточием. Отреагируй на действия всех игроков "
            "этого хода в одном связном повествовании, обращаясь к каждому по "
            "имени там, где это уместно.\n"
            "\n"
            "ПРИВАТНЫЕ ДЕЙСТВИЯ. Если строка помечена «(приватно)», это значит, "
            "что игрок действует скрытно от остальных участников партии "
            "(крадётся, подслушивает, проверяет карман, шепчет кому-то). "
            "Опиши результат ТОЛЬКО этому игроку, не раскрывая его намерений "
            "и последствий остальным. В конце ответа всё равно пришли блок "
            "[ACTIONS], но исходи из того, что о приватной части партии знает "
            "только сам игрок.\n"
        )

    moderation_block = MODERATION_MODES.get(
        getattr(cfg, "moderation", "none"), ""
    )

    equipment_lines = []

    def _fmt_state(label, st):
        if st is None:
            return
        eq = getattr(st, "equipped", {}) or {}
        inv = getattr(st, "inventory", []) or []
        equipped_items = []
        for sid, slabel in EQUIPMENT_SLOTS:
            it = eq.get(sid)
            if it:
                equipped_items.append(f"    – {slabel}: {it.get('name', '?')}")
        if equipped_items or inv:
            equipment_lines.append(f"  {label}:")
            if equipped_items:
                equipment_lines.append("    Снаряжено:")
                equipment_lines.extend(equipped_items)
            if inv:
                inv_names = ", ".join((it.get("name") or "?") for it in inv[:15])
                suffix = "" if len(inv) <= 15 else f" …(ещё {len(inv) - 15})"
                equipment_lines.append(f"    В рюкзаке: {inv_names}{suffix}")

    if player_state is not None:
        _fmt_state("Главный герой" if not multiplayer else "Ваш персонаж",
                   player_state)
    if other_players:
        for name, st in other_players.items():
            _fmt_state(f"Игрок {name}", st)

    equipment_block = ""
    if equipment_lines:
        equipment_block = (
            "\nЭКИПИРОВКА И ИНВЕНТАРЬ ПЕРСОНАЖЕЙ (учитывай в описаниях: "
            "если у героя есть меч — он может рубить, если щит — защищаться и т.п.):\n"
            + "\n".join(equipment_lines) + "\n"
        )

    # --- Известные NPC ---
    npc_block = ""
    if card_store is not None:
        npcs = []
        for c in getattr(card_store, "cards", []):
            if not isinstance(c, dict):
                continue
            if str(c.get("type", "")).lower() != "существо":
                continue
            if str(c.get("status", "")).lower() == "мёртв":
                continue
            char = (c.get("character") or "").strip()
            goal = (c.get("goal") or "").strip()
            if not char and not goal:
                continue
            npcs.append([c.get("name", "?"), char, goal,
                         c.get("status", ""), c.get("attitude", "")])
        if npcs:
            lines = [
                "\nИЗВЕСТНЫЕ NPC (сохраняй их характер и цели в диалогах; "
                "если NPC противоречит своему характеру — объясни почему):"
            ]
            for name, char, goal, status, attitude in npcs[:20]:
                bits = [f"  – {name}"]
                tags = []
                if status:
                    tags.append(status)
                if attitude:
                    tags.append(attitude)
                if tags:
                    bits.append(f"({', '.join(tags)})")
                if char:
                    bits.append(f"— характер: {char}")
                if goal:
                    bits.append(f"; цель: {goal}")
                lines.append(" ".join(bits))
            npc_block = "\n".join(lines) + "\n"

    quests_block = ""
    if quest_store is not None:
        active_quests = quest_store.active()
        if active_quests:
            lines = [
                "\nАКТИВНЫЕ КВЕСТЫ ГЕРОЯ (держи их в уме, но НЕ пересказывай "
                "игроку списком — просто помни, куда движется история):"
            ]
            for q in active_quests:
                desc = (q.get("description") or "").strip()
                if desc:
                    lines.append(f"  – {q['name']}: {desc}")
                else:
                    lines.append(f"  – {q['name']}")
            quests_block = "\n".join(lines) + "\n"

    # --- Важные факты (редактируемая память) ---
    facts_block = ""
    if important_facts:
        clean = [str(f).strip() for f in important_facts if str(f).strip()]
        if clean:
            lines = [
                "\nВАЖНЫЕ ФАКТЫ О МИРЕ И СЮЖЕТЕ (редактируется игроком — "
                "считай это каноном; НЕ пересказывай их списком, "
                "просто согласуй с ними повествование):"
            ]
            for i, f in enumerate(clean, 1):
                lines.append(f"  {i}. {f}")
            facts_block = "\n".join(lines) + "\n"

    # --- Характеристики героя ---
    stats_block = ""
    if player_state is not None and hasattr(player_state, "get_effective_stats"):
        try:
            eff = player_state.get_effective_stats()
        except Exception:
            eff = {}
        if eff:
            base = getattr(player_state, "stats", {}) or {}
            lines = [
                "\nХАРАКТЕРИСТИКИ ГЕРОЯ (учитывай в описаниях: сильный герой "
                "легче поднимает тяжести, ловкий — легче уклоняется, умный — "
                "замечает детали и т.п.):"
            ]
            for k, v in eff.items():
                b = base.get(k)
                if b is not None and b != v:
                    lines.append(f"  – {k}: {v} (база {b}, с экипировкой)")
                else:
                    lines.append(f"  – {k}: {v}")
            stats_block = "\n".join(lines) + "\n"

    # --- Локации и карта ---
    locations_block = ""
    if location_store is not None and location_store.locations:
        known = location_store.locations
        lines = []
        if current_location:
            cur = location_store.find(current_location)
            lines.append(f"\nТЕКУЩАЯ ЛОКАЦИЯ ГЕРОЯ: {current_location}")
            if cur and cur.get("description"):
                lines.append(f"  {cur['description']}")
        else:
            lines.append("\nТЕКУЩАЯ ЛОКАЦИЯ ГЕРОЯ: пока не определена")

        lines.append(
            "\nКАРТА МИРА (известные локации; [✓] — посещённые, [?] — "
            "упомянутые, но не посещённые):"
        )
        for loc in known:
            mark = "✓" if loc.get("discovered", True) else "?"
            desc = (loc.get("description") or "").strip()
            conns = loc.get("connections") or []
            entry = f"  [{mark}] {loc['name']}"
            if desc:
                entry += f": {desc}"
            if conns:
                entry += f" (соединения: {', '.join(conns)})"
            lines.append(entry)
        locations_block = "\n".join(lines) + "\n"

    # --- Хуки плагинов ---
    plugin_block = ""
    if plugin_prompt_hooks:
        chunks = []
        for hook in plugin_prompt_hooks:
            try:
                out = hook(plugin_context or {})
            except Exception:
                out = None
            if out:
                chunks.append(str(out).rstrip())
        if chunks:
            plugin_block = "\n" + "\n".join(chunks) + "\n"

    # --- RPG-инструкции ---
    rpg_block = ""
    if bool(getattr(cfg, "rpg_mode", False)):
        lines = [
            "\nRPG-РЕЖИМ ВКЛЮЧЁН. Действия с риском и неопределённостью "
            "(атаки, взлом, убеждение, скрытность, акробатика, сопротивление) "
            "НЕ РЕШАЙ САМ — запрашивай бросок кубика. Формат:",
            "[ROLL]характеристика|сложность[/ROLL]",
            "   Характеристики: " + ", ".join(STAT_NAMES) + ".",
            "   Сложность — целое, обычно 8–18: 8 — просто, 12 — средне, "
            "16 — трудно, 20 — почти невозможно.",
            "   Необязательный третий сегмент после | — короткая метка проверки "
            "для читателя, например: [ROLL]сила|13|Атака по гоблину[/ROLL].",
            "   После тега — НЕ описывай исход броска, жди результат. "
            "Приложение бросит d20, прибавит характеристику с бонусами "
            "экипировки и вернёт строку вида "
            "«сила: 15 + 3 = 18 против 13 — успех».",
            "   Только после получения результата описывай последствия.",
            "   Не запрашивай броски на тривиальные действия (осмотреться, "
            "поговорить без давления, идти по дороге).",
        ]
        rpg_block = "\n".join(lines) + "\n"

    return (
        "Ты — опытный гейм-мастер текстового квеста и соавтор истории.\n"
        "\n"
        "НАСТРОЙКИ ИСТОРИИ:\n"
        f"Название: {cfg.title}\n"
        f"Жанр/тон: {cfg.genre}\n"
        f"Мир и сеттинг: {cfg.setting}\n"
        f"Завязка сюжета: {cfg.premise}\n"
        f"Главный герой: {cfg.hero_name} — {cfg.hero_desc}\n"
        f"Сложность/стиль повествования: {cfg.style}\n"
        f"{summary_block}"
        f"{facts_block}"
        f"{quests_block}"
        f"{npc_block}"
        f"{stats_block}"
        f"{equipment_block}"
        f"{locations_block}"
        f"{plugin_block}"
        f"{multiplayer_block}"
        f"{moderation_block}"
        f"{rpg_block}"
        "\n"
        "ПРАВИЛА:\n"
        "1. Веди повествование от второго или третьего лица, живо и образно, "
        "на русском языке. Длина хода: "
        + TURN_LENGTHS.get(turn_length, TURN_LENGTHS[DEFAULT_TURN_LENGTH])
        + ".\n"
        "2. Реагируй на действия игрока логично и последовательно, помни контекст "
        "и учитывай, что у героев есть при себе перечисленные предметы.\n"
        "3. Когда в сюжете появляется НОВЫЙ значимый предмет или существо "
        "(артефакт, монстр, союзник, ключевой персонаж), обязательно опиши его "
        "отдельной карточкой в конце сообщения в формате:\n"
        "[CARD]\n"
        '{"type": "предмет", "name": "Название", '
        '"description": "Краткое описание для читателя", '
        '"properties": {"важное свойство": "значение"}, '
        '"equip_slot": "weapon"}\n'
        "[/CARD]\n"
        "   Поле \"type\" — \"предмет\" или \"существо\". Поле \"equip_slot\" "
        "необязательно, но желательно для носимых предметов — одно из: "
        + ", ".join(sid for sid, _ in EQUIPMENT_SLOTS) + ".\n"
        "\n"
        "   ДОПОЛНИТЕЛЬНЫЕ НЕОБЯЗАТЕЛЬНЫЕ ПОЛЯ (очень помогают миру "
        "оставаться связным — используй их, когда уместно):\n"
        "     * \"status\"   — для предметов и существ: \"жив\", \"мёртв\", "
        "\"потерян\", \"уничтожен\", \"неизвестно\". Если существо погибает, "
        "а предмет теряется или ломается — пришли карточку с ТЕМ ЖЕ именем "
        "и новым значением status; мир обновится, а не создастся дубликат.\n"
        "     * \"attitude\" — для существ: \"союзник\", \"нейтрал\", \"враг\", "
        "\"неизвестно\". Меняй, если отношение к герою меняется.\n"
        "     * \"hp\"       — для существ: число, например 12. Уменьшай при "
        "получении ран, обнуляй при смерти вместе с status: \"мёртв\".\n"
        "     * \"location\" — короткое название локации, где сейчас находится "
        "карточка (например «Таверна», «Тёмный лес»). Помогает потом понять, "
        "что рядом с героем.\n"
        "     * \"character\" — для существ: 1-2 предложения о характере, "
        "манере речи, привычках. Обязательно для значимых NPC.\n"
        "     * \"goal\"      — для существ: чего NPC хочет от героя "
        "или от мира. Тоже обязательно для значимых NPC.\n"
        "4. Когда в сюжете появляется НОВАЯ ЦЕЛЬ или ЗАДАЧА для героя "
        "(спасти кого-то, найти предмет, добраться до места, разгадать тайну), "
        "добавляй в конце сообщения блок-квест:\n"
        "[QUEST]Название|Краткое описание цели|active[/QUEST]\n"
        "   Поле статуса — строго одно из: active, done, failed.\n"
        "   Когда квест завершается, пришли [QUEST] с ТЕМ ЖЕ названием и "
        "новым статусом: done при успехе, failed при провале; запись в "
        "журнале обновится, дубликат не создастся.\n"
        "5. В самом конце КАЖДОГО ответа всегда добавляй блок с 2-4 вариантами "
        "дальнейших действий игрока в формате:\n"
        "[ACTIONS]Вариант 1|Вариант 2|Вариант 3[/ACTIONS]\n"
        "   Варианты должны быть краткими (3-6 слов), разнообразными.\n"
        "6. Когда герой ПЕРЕМЕЩАЕТСЯ в новую локацию или оказывается в "
        "значимом месте, добавь в конце сообщения блок:\n"
        "[LOCATION]{\"name\": \"Название\", \"description\": \"Краткое описание\", "
        "\"connections\": [\"Сосед-1\", \"Сосед-2\"], \"current\": true}[/LOCATION]\n"
        "   \"current\": true означает, что герой СЕЙЧАС находится здесь. "
        "Если локация уже известна и просто упоминается без перемещения — "
        "можно прислать её без current или не присылать вообще. "
        "Соседние локации, которых ещё нет на карте, автоматически появятся "
        "как «серые» точки до первого визита.\n"
        "7. Никогда не объясняй читателю сами теги/формат — просто используй их.\n"
    )

# ---------------------------------------------------------------------------
# Безопасный разбор JSON (защита от «JSON-bomb»)
# ---------------------------------------------------------------------------

def _json_depth(obj, current: int = 0, limit: int = MAX_JSON_DEPTH * 2) -> int:
    """
    Максимальная глубина вложенности.
    Ограничен `limit`, чтобы не уйти в бесконечность на патологических данных.
    """
    if current >= limit:
        return current
    if isinstance(obj, dict):
        if not obj:
            return current + 1
        return max(_json_depth(v, current + 1, limit) for v in obj.values())
    if isinstance(obj, list):
        if not obj:
            return current + 1
        return max(_json_depth(v, current + 1, limit) for v in obj)
    return current


def _safe_json_loads(text, max_bytes: int = MAX_JSON_BYTES,
                     max_depth: int = MAX_JSON_DEPTH):
    """
    Парсит JSON с ограничениями по размеру и глубине.

    Возвращает (value, error_message).
      * value=None, error="" — пустой ввод.
      * value=None, error!="" — ошибка.
      * value=<parsed>, error="" — успех.
    """
    if text is None:
        return None, ""
    if not isinstance(text, str):
        text = str(text)
    text = text.strip()
    if not text:
        return None, ""

    # Проверяем размер в байтах, а не в символах — не доверяем UTF-8.
    try:
        size = len(text.encode("utf-8", errors="replace"))
    except Exception:
        return None, "не удалось определить размер"
    if size > max_bytes:
        return None, f"JSON слишком большой ({size} > {max_bytes} байт)"

    try:
        data = json.loads(text)
    except json.JSONDecodeError as e:
        return None, f"ошибка JSON: {e}"
    except Exception as e:
        return None, f"ошибка разбора: {e}"

    depth = _json_depth(data)
    if depth > max_depth:
        return None, f"слишком глубокая вложенность ({depth} > {max_depth})"

    return data, ""


def _clip_str(value, max_len: int) -> str:
    """Обрезает строку до max_len, безопасно для не-строк."""
    if value is None:
        return ""
    try:
        s = str(value)
    except Exception:
        return ""
    if len(s) > max_len:
        return s[:max_len] + "…"
    return s

def _parse_quest_raw(raw: str):
    """
    Разбирает содержимое [QUEST]...[/QUEST].

    Поддерживает два формата:
      * pipe-формат:  Название|Описание|status
      * JSON-объект:  {"name": ..., "description": ..., "status": ...}

    Возвращает dict или None.
    """
    raw = (raw or "").strip()
    if not raw:
        return None

    # JSON-вариант
    if raw.startswith("{"):
        data, _err = _safe_json_loads(raw)
        if isinstance(data, dict) and data.get("name"):
            status = str(data.get("status", "active")).strip().lower()
            return {
                "name": _clip_str(data["name"], MAX_CARD_NAME_LEN).strip(),
                "description": _clip_str(
                    data.get("description", ""), MAX_CARD_DESC_LEN
                ).strip(),
                "status": QUEST_STATUS_ALIASES.get(status, "active"),
            }

    # Pipe-вариант
    parts = [p.strip() for p in raw.split("|")]
    if not parts or not parts[0]:
        return None
    name = parts[0]
    description = ""
    status = "active"

    if len(parts) == 1:
        pass
    elif len(parts) == 2:
        second = parts[1].lower()
        if second in QUEST_STATUS_ALIASES:
            status = second
        else:
            description = parts[1]
    else:
        # ≥3 частей: последняя — статус, всё между — описание
        # (описание может содержать "|" — склеиваем обратно).
        status = parts[-1].lower()
        description = "|".join(parts[1:-1]).strip()

    return {
        "name": name,
        "description": description,
        "status": QUEST_STATUS_ALIASES.get(status, "active"),
    }

def _parse_stats_text(text: str) -> dict:
    """
    «сила:10, ловкость:12, интеллект:8» → {"сила": 10, "ловкость": 12, ...}
    Разделители — «:» или «=»; лишнее игнорируется.
    """
    result = {}
    for part in (text or "").split(","):
        part = part.strip()
        if not part:
            continue
        if ":" in part:
            k, _, v = part.partition(":")
        elif "=" in part:
            k, _, v = part.partition("=")
        else:
            continue
        k, v = k.strip(), v.strip()
        if not k:
            continue
        try:
            result[k] = int(v)
        except ValueError:
            continue
    return result


def _parse_roll_raw(raw: str):
    """
    Разбирает [ROLL]...[/ROLL].

    Форматы:
      * pipe:  сила|15            — базовая проверка
      * pipe:  сила|15|Атака      — с меткой
      * JSON:  {"stat": "сила", "dc": 15, "label": "Атака"}

    Возвращает {"stat": str, "dc": int, "label": str} или None.
    """
    raw = (raw or "").strip()
    if not raw:
        return None

    if raw.startswith("{"):
        data, _err = _safe_json_loads(raw)
        if isinstance(data, dict):
            stat = str(data.get("stat") or data.get("check") or "").strip()
            dc_raw = (data.get("dc") or data.get("difficulty")
                      or data.get("target"))
            try:
                dc = int(dc_raw)
            except (TypeError, ValueError):
                return None
            if not stat:
                return None
            return {
                "stat": stat,
                "dc": dc,
                "label": str(data.get("label", "")).strip(),
            }

    parts = [p.strip() for p in raw.split("|")]
    if len(parts) < 2:
        return None
    stat = parts[0]
    try:
        dc = int(parts[1])
    except (TypeError, ValueError):
        return None
    label = "|".join(parts[2:]).strip() if len(parts) > 2 else ""
    return {"stat": stat, "dc": dc, "label": label}

def _parse_location_raw(raw: str):
    """
    Разбирает [LOCATION]...[/LOCATION].

    Форматы:
      * JSON: {"name": "...", "description": "...",
               "connections": ["A", "B"], "current": true}
      * pipe: Название|Описание|Сосед1,Сосед2|current

    Возвращает {"name", "description", "connections", "current"} или None.
    """
    raw = (raw or "").strip()
    if not raw:
        return None

    if raw.startswith("{"):
        data, _err = _safe_json_loads(raw)
        if isinstance(data, dict) and data.get("name"):
            conns = data.get("connections") or []
            if isinstance(conns, str):
                conns = [c.strip() for c in conns.split(",") if c.strip()]
            elif not isinstance(conns, list):
                conns = []
            return {
                "name": str(data["name"]).strip(),
                "description": str(data.get("description", "")).strip(),
                "connections": [str(c).strip() for c in conns if str(c).strip()],
                "current": bool(data.get("current", False)),
            }

    parts = [p.strip() for p in raw.split("|")]
    if not parts or not parts[0]:
        return None
    name = parts[0]
    description = parts[1] if len(parts) > 1 else ""
    conns = []
    if len(parts) > 2:
        conns = [c.strip() for c in parts[2].split(",") if c.strip()]
    current = False
    if len(parts) > 3:
        current = parts[3].strip().lower() in ("current", "true", "1", "да", "здесь")
    return {
        "name": name,
        "description": description,
        "connections": conns,
        "current": current,
    }

# ---------------------------------------------------------------------------
# Голосовые хелперы
# ---------------------------------------------------------------------------

def _check_tts_available() -> tuple:
    """Возвращает (available: bool, message: str)."""
    try:
        import pyttsx3  # noqa: F401
    except ImportError:
        return False, ("Библиотека pyttsx3 не установлена. "
                       "Выполните: pip install pyttsx3")
    return True, ""


def _check_stt_available() -> tuple:
    """Возвращает (available: bool, message: str)."""
    try:
        import speech_recognition  # noqa: F401
    except ImportError:
        return False, ("Библиотека SpeechRecognition не установлена. "
                       "Выполните: pip install SpeechRecognition pyaudio")
    return True, ""


def _split_for_tts(text: str, max_len: int = TTS_MAX_CHUNK) -> list:
    """
    Делит длинный текст на куски по границам предложений.
    pyttsx3 плохо переносит очень длинные строки — особенно на Windows.
    """
    text = (text or "").strip()
    if not text:
        return []
    # Сначала — по предложениям
    parts = re.split(r'(?<=[.!?…])\s+', text)
    chunks = []
    buf = ""
    for p in parts:
        p = p.strip()
        if not p:
            continue
        if not buf:
            buf = p
        elif len(buf) + 1 + len(p) <= max_len:
            buf += " " + p
        else:
            chunks.append(buf)
            buf = p
    if buf:
        chunks.append(buf)

    # На всякий случай добиваем слишком длинные куски по пробелам
    final = []
    for ch in chunks:
        while len(ch) > max_len:
            cut = ch.rfind(" ", 0, max_len)
            if cut <= 0:
                cut = max_len
            final.append(ch[:cut].strip())
            ch = ch[cut:].strip()
        if ch:
            final.append(ch)
    return final


def _listen_and_recognize(on_result, on_error, on_status):
    """
    Запускается в фоновом потоке.

    Колбэки вызываются из ЭТОГО потока — вызывающий обязан обернуть их
    в self.after(0, ...) для безопасного обновления Tk.
    """
    ok, msg = _check_stt_available()
    if not ok:
        on_error(msg)
        return

    import speech_recognition as sr

    try:
        recognizer = sr.Recognizer()
        with sr.Microphone() as source:
            on_status("Слушаю...")
            try:
                recognizer.adjust_for_ambient_noise(source, duration=0.4)
            except Exception:
                pass
            audio = recognizer.listen(source, timeout=8, phrase_time_limit=15)
    except sr.WaitTimeoutError:
        on_error("Тишина — попробуйте снова.")
        return
    except Exception as e:
        on_error(f"Ошибка записи: {e}")
        return

    on_status("Распознаю...")
    try:
        text = recognizer.recognize_google(audio, language=STT_LANGUAGE)
        on_result(text.strip())
    except sr.UnknownValueError:
        on_error("Речь не распознана.")
    except sr.RequestError as e:
        on_error(f"Сервис распознавания недоступен: {e}")
    except Exception as e:
        on_error(f"Ошибка распознавания: {e}")

# ---------------------------------------------------------------------------
# Логи и статистика
# ---------------------------------------------------------------------------

class AppLogger:
    """
    Простой потокобезопасный журнал ошибок в ~/.quest_ai/logs/errors.log.

    Формат записи:
      ===== 2026-01-01 12:00:00 — ai =====
      Класс: RuntimeError
      Сообщение: ...
      Контекст: {...}
      --- traceback ---
      ...
      --- последний промпт ---
      ...
      --- последний ответ ---
      ...
    """

    def __init__(self, log_file: str = ERROR_LOG_FILE,
                 max_bytes: int = ERROR_LOG_MAX_BYTES):
        self.log_file = log_file
        self.max_bytes = int(max_bytes) if max_bytes else 0
        self._lock = threading.Lock()

    def log_error(self, category: str, exc: BaseException,
                  extra: dict = None):
        """
        category — короткая метка («ai», «ui», «network», «save»).
        exc      — исключение.
        extra    — словарь с произвольными деталями (prompt, response, etc.)
        """
        try:
            self._rotate_if_needed()
            ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            parts = [f"===== {ts} — {category} ====="]
            parts.append(f"Класс: {type(exc).__name__}")
            parts.append(f"Сообщение: {exc}")

            if extra:
                for key, val in extra.items():
                    try:
                        text = str(val)
                    except Exception:
                        text = "<unprintable>"
                    if key in ("prompt", "response"):
                        text = self._short(text, LOG_PROMPT_HEAD)
                    parts.append(f"{key}: {text}")

            tb = "".join(traceback.format_exception(
                type(exc), exc, exc.__traceback__
            ))
            parts.append("--- traceback ---")
            parts.append(tb.rstrip())

            parts.append("")
            with self._lock:
                with open(self.log_file, "a", encoding="utf-8") as f:
                    f.write("\n".join(parts) + "\n\n")
        except Exception:
            # Логгер сам не должен ломать приложение.
            pass

    def log_event(self, category: str, message: str, extra: dict = None):
        """Не-ошибочные события, которые тоже полезно видеть в логе."""
        try:
            self._rotate_if_needed()
            ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            parts = [f"----- {ts} — {category} -----", message]
            if extra:
                for key, val in extra.items():
                    parts.append(f"{key}: {self._short(str(val), 400)}")
            parts.append("")
            with self._lock:
                with open(self.log_file, "a", encoding="utf-8") as f:
                    f.write("\n".join(parts) + "\n\n")
        except Exception:
            pass

    def _rotate_if_needed(self):
        if not self.max_bytes:
            return
        try:
            if os.path.exists(self.log_file) \
                    and os.path.getsize(self.log_file) > self.max_bytes:
                old = self.log_file + ".old"
                try:
                    if os.path.exists(old):
                        os.remove(old)
                except OSError:
                    pass
                os.replace(self.log_file, old)
        except Exception:
            pass

    @staticmethod
    def _short(text: str, max_len: int) -> str:
        if text is None:
            return ""
        s = str(text)
        if len(s) <= max_len:
            return s
        return s[:max_len] + f"\n…(+{len(s) - max_len} симв.)"


class SessionStats:
    """
    Статистика сессии:
      * turns            — сколько ходов ИИ сгенерировал;
      * chars_in / out   — сколько символов ввёл игрок / получил от ИИ;
      * tokens_in / out  — из usage провайдера (если он его вернул);
      * tokens_reports   — сколько ответов содержали usage (для статистики);
      * errors           — сколько ошибок ИИ за сессию.
    """

    def __init__(self):
        self.turns = 0
        self.chars_in = 0
        self.chars_out = 0
        self.tokens_in = 0
        self.tokens_out = 0
        self.tokens_reports = 0
        self.errors = 0

    def to_dict(self):
        return {
            "turns": int(self.turns),
            "chars_in": int(self.chars_in),
            "chars_out": int(self.chars_out),
            "tokens_in": int(self.tokens_in),
            "tokens_out": int(self.tokens_out),
            "tokens_reports": int(self.tokens_reports),
            "errors": int(self.errors),
        }

    @staticmethod
    def from_dict(d):
        s = SessionStats()
        if isinstance(d, dict):
            for key in ("turns", "chars_in", "chars_out",
                        "tokens_in", "tokens_out",
                        "tokens_reports", "errors"):
                try:
                    setattr(s, key, int(d.get(key, 0) or 0))
                except (TypeError, ValueError):
                    pass
        return s

    def add_turn(self, user_message: str, reply: str, usage: dict = None):
        self.turns += 1
        self.chars_in += len(user_message or "")
        self.chars_out += len(reply or "")
        if usage:
            try:
                ti = int(usage.get("prompt_tokens") or 0)
                to = int(usage.get("completion_tokens") or 0)
            except (TypeError, ValueError):
                ti = to = 0
            if ti or to:
                self.tokens_in += ti
                self.tokens_out += to
                self.tokens_reports += 1

    def estimate_cost(self, provider_id: str):
        """
        Возвращает (currency, cost) или (None, None), если тарифа нет.
        Стоимость считается по СУММЕ накопленных токенов и текущему
        прайсу провайдера — это оценка «как если бы всё шло через него».
        """
        pricing = PROVIDER_PRICING.get(provider_id)
        if not pricing or not self.tokens_reports:
            return None, None
        currency, p_in, p_out = pricing
        if currency == "—":
            return currency, 0.0
        cost = (self.tokens_in / 1_000_000.0) * float(p_in) \
             + (self.tokens_out / 1_000_000.0) * float(p_out)
        return currency, cost

# ---------------------------------------------------------------------------
# Плагины
# ---------------------------------------------------------------------------

class PluginAPI:
    """
    API, передаваемый каждому плагину в register(api).

    Плагин может зарегистрировать:
      * собственные теги вида [TAG]...[/TAG] — api.register_tag(...)
      * хук, возвращающий текст для system prompt — api.register_prompt_hook(...)
      * хук, вызываемый после каждого хода ИИ — api.register_turn_end_hook(...)
      * новый текстовый провайдер — api.register_provider(...)

    Все данные, которые плагин хочет сохранить между ходами и пережить
    сохранение игры, складываются в api.state (обычный dict, JSON-совместимый).
    Ключи рекомендуется неймспейсить именем плагина:

        api.state.setdefault("myplugin", {})["counter"] = 0
    """

    def __init__(self, logger=None):
        self.tags = {}             # "WEATHER" -> handler(raw, ctx) -> Any
        self.prompt_hooks = []     # fn(context) -> str
        self.turn_end_hooks = []   # fn(context) -> None
        self.providers = {}        # provider_id -> handler(prompt, history, t, mt, tp)
        self.state = {}            # свободный namespace
        self.logger = logger
        self._plugin_name = None

    # -- Регистрация -------------------------------------------------------

    def register_tag(self, name: str, handler):
        """Регистрирует [NAME]...[/NAME]. Handler: (raw, ctx) -> Any."""
        if not name or not callable(handler):
            return
        self.tags[str(name).upper()] = handler

    def register_prompt_hook(self, handler):
        """Hook: fn(context) -> str. Возвращённая строка попадает в промпт."""
        if callable(handler):
            self.prompt_hooks.append(handler)

    def register_turn_end_hook(self, handler):
        """Hook: fn(context) -> None. Вызывается после каждого хода ИИ."""
        if callable(handler):
            self.turn_end_hooks.append(handler)

    def register_provider(self, provider_id: str, info: dict, handler):
        """
        Регистрирует нового текстового провайдера.

        info — как элементы TEXT_PROVIDERS: {label, model, signup_url, ...}
        handler(system_prompt, history, temperature, max_tokens, top_p)
            -> (content: str, usage: dict)
        """
        if not provider_id or not callable(handler):
            return
        provider_id = str(provider_id)
        info = dict(info or {})
        info.setdefault("label", provider_id)
        info.setdefault("model", "")
        info["kind"] = PLUGIN_PROVIDER_KIND
        TEXT_PROVIDERS[provider_id] = info
        self.providers[provider_id] = handler

    # -- Вспомогательное ---------------------------------------------------

    def log_info(self, message: str):
        if self.logger is not None:
            try:
                prefix = f"[{self._plugin_name}] " if self._plugin_name else ""
                self.logger.log_event("plugin", f"{prefix}{message}")
            except Exception:
                pass

    def log_error(self, message: str, exc: BaseException = None):
        if self.logger is not None:
            try:
                prefix = f"[{self._plugin_name}] " if self._plugin_name else ""
                if exc is None:
                    self.logger.log_event("plugin", f"{prefix}{message}")
                else:
                    self.logger.log_error(
                        "plugin", exc, {"plugin_message": prefix + str(message)},
                    )
            except Exception:
                pass


class PluginManager:
    """
    Сканирует MODS_DIR, импортирует каждый .py и вызывает register(api).

    * Файлы, начинающиеся с '_', игнорируются.
    * Ошибки одного плагина не мешают загрузке остальных.
    * api.state сохраняется вместе с игрой (см. MainApp._build_game_state).
    """

    def __init__(self, mods_dir: str = MODS_DIR, logger=None):
        self.mods_dir = mods_dir
        os.makedirs(self.mods_dir, exist_ok=True)
        self.logger = logger
        self.api = PluginAPI(logger=logger)
        self.loaded = []          # [(file_name, plugin_label)]
        self.errors = []          # [(file_name, error_message)]

    # -- Публичное ---------------------------------------------------------

    def load_all(self):
        self._ensure_readme()
        self.api = PluginAPI(logger=self.logger)
        self.loaded = []
        self.errors = []

        pattern = os.path.join(self.mods_dir, "*.py")
        for path in sorted(glob.glob(pattern)):
            base = os.path.basename(path)
            if base.startswith("_"):
                continue
            self._load_one(path, base)

    def reload(self):
        """Перезагружает плагины, сохраняя api.state между версиями."""
        old_state = dict(self.api.state) if hasattr(self.api, "state") else {}
        self.load_all()
        self.api.state.update(old_state)

    def get_tag_handlers(self) -> dict:
        return dict(self.api.tags)

    def get_prompt_hooks(self) -> list:
        return list(self.api.prompt_hooks)

    def get_turn_end_hooks(self) -> list:
        return list(self.api.turn_end_hooks)

    def get_providers(self) -> dict:
        return dict(self.api.providers)

    def summary(self) -> str:
        lines = []
        lines.append(f"Папка модов: {self.mods_dir}")
        if self.loaded:
            lines.append("")
            lines.append("Загруженные плагины:")
            for fname, label in self.loaded:
                lines.append(f"  – {label}  ({fname})")
        else:
            lines.append("")
            lines.append("Загруженных плагинов нет.")
        if self.errors:
            lines.append("")
            lines.append("Ошибки при загрузке:")
            for fname, err in self.errors:
                lines.append(f"  – {fname}: {err}")
        lines.append("")
        lines.append(
            f"Теги: {len(self.api.tags)}, "
            f"prompt-хуки: {len(self.api.prompt_hooks)}, "
            f"turn-end хуки: {len(self.api.turn_end_hooks)}, "
            f"провайдеры: {len(self.api.providers)}."
        )
        return "\n".join(lines)

    # -- Приватное ---------------------------------------------------------

    def _load_one(self, path: str, base: str):
        # Уникальное имя модуля, чтобы избежать коллизий.
        module_name = f"quest_ai_mod_{os.path.splitext(base)[0]}"
        try:
            spec = importlib.util.spec_from_file_location(module_name, path)
            if spec is None or spec.loader is None:
                self.errors.append((base, "не удалось создать spec"))
                return
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
        except Exception as e:
            self.errors.append((base, f"ошибка импорта: {e}"))
            if self.logger is not None:
                self.logger.log_error("plugin", e, {"file": base})
            return

        register_fn = getattr(module, "register", None)
        if not callable(register_fn):
            self.errors.append((base, "нет функции register(api)"))
            return

        label = getattr(module, "PLUGIN_NAME", None) or os.path.splitext(base)[0]

        prev_name = self.api._plugin_name
        self.api._plugin_name = label
        try:
            register_fn(self.api)
        except Exception as e:
            self.errors.append((base, f"ошибка в register(): {e}"))
            if self.logger is not None:
                self.logger.log_error("plugin", e, {"file": base, "plugin": label})
            return
        finally:
            self.api._plugin_name = prev_name

        self.loaded.append((base, label))

    def _ensure_readme(self):
        if os.path.exists(MODS_README):
            return
        try:
            with open(MODS_README, "w", encoding="utf-8") as f:
                f.write(SAMPLE_PLUGIN_README)
        except Exception:
            pass

SAMPLE_PLUGIN_README = """# Плагины Text Quest AI

Поместите сюда `.py`-файлы. Каждый файл должен определять функцию `register(api)`.
При запуске игры все `.py` из этой папки будут импортированы и `register()` будет
вызван один раз.

Файлы, начинающиеся с `_`, игнорируются."""

SAMPLE_WEATHER_PLUGIN = """"""

def _fmt_num(n: int) -> str:
    try:
        n = int(n)
    except (TypeError, ValueError):
        return "0"
    if n < 1000:
        return str(n)
    if n < 1_000_000:
        return f"{n / 1000.0:.1f}k"
    return f"{n / 1_000_000.0:.2f}M"

# ---------------------------------------------------------------------------
# Markdown-рендеринг в Text/Listbox
# ---------------------------------------------------------------------------

def _insert_markdown(text_widget, text, base_tags=()):
    """
    Вставляет строку в Text, распознавая **bold**, *italic* и `code`.
    base_tags — дополнительные теги, применяемые ко всем фрагментам.
    """
    if not text:
        return
    for part in MD_PATTERN.split(text):
        if not part:
            continue
        tags = list(base_tags)
        if part.startswith("**") and part.endswith("**") and len(part) > 4:
            tags.append("md_bold")
            part = part[2:-2]
        elif part.startswith("*") and part.endswith("*") and len(part) > 2:
            tags.append("md_italic")
            part = part[1:-1]
        elif part.startswith("`") and part.endswith("`") and len(part) > 2:
            tags.append("md_code")
            part = part[1:-1]
        text_widget.insert("end", part, tuple(tags))


def parse_ai_response(text: str, plugin_tags: dict = None):
    """
    Разбирает ответ ИИ.

    plugin_tags — dict {TAG_NAME: handler(raw, ctx)} от PluginManager.
    Для каждого тега ищет [TAG_NAME]...[/TAG_NAME], вызывает handler,
    результаты складывает в plugin_data. Теги вырезаются из narrative.

    Возвращает:
      narrative, actions, cards, quests, rolls, locations, plugin_data
    """
    actions = []
    m = ACTIONS_RE.search(text)
    if m:
        raw = m.group(1)
        actions = [a.strip() for a in raw.split("|") if a.strip()]

    cards = []
    for m in CARD_RE.finditer(text):
        raw = m.group(1).strip()
        # Защита от JSON-бомб: ограничение размера и глубины.
        try:
            card, err = _safe_json_loads(raw)
        except NameError:
            # На случай, если _safe_json_loads ещё не определена —
            # откатываемся на обычный json.loads.
            card, err = None, ""
            try:
                card = json.loads(raw)
            except json.JSONDecodeError:
                card = None
        if err or not isinstance(card, dict):
            continue
        cards.append(card)

    quests = []
    for m in QUEST_RE.finditer(text):
        q = _parse_quest_raw(m.group(1))
        if q:
            quests.append(q)

    rolls = []
    for m in ROLL_RE.finditer(text):
        r = _parse_roll_raw(m.group(1))
        if r:
            rolls.append(r)

    locations = []
    for m in LOCATION_RE.finditer(text):
        l = _parse_location_raw(m.group(1))
        if l:
            locations.append(l)

    # --- Плагинные теги ---
    plugin_data = {}
    if plugin_tags:
        for name, handler in plugin_tags.items():
            try:
                pattern = re.compile(
                    r"\[" + re.escape(name) + r"](.*?)\[/" + re.escape(name) + r"]",
                    re.DOTALL | re.IGNORECASE,
                )
            except re.error:
                continue
            parsed_for_tag = []
            for m in pattern.finditer(text):
                try:
                    result = handler(m.group(1).strip(), {})
                except Exception:
                    result = None
                if result is not None:
                    parsed_for_tag.append(result)
            if parsed_for_tag:
                plugin_data[name] = parsed_for_tag
            # Вырезаем теги из повествования, чтобы не засорять UI.
            try:
                text = pattern.sub("", text)
            except re.error:
                pass

    narrative = ACTIONS_RE.sub("", text)
    narrative = CARD_RE.sub("", narrative)
    narrative = QUEST_RE.sub("", narrative)
    narrative = ROLL_RE.sub("", narrative)
    narrative = LOCATION_RE.sub("", narrative).strip()
    return narrative, actions, cards, quests, rolls, locations, plugin_data


@dataclass
class StoryConfig:
    title: str = "Новая история"
    genre: str = "фэнтези"
    setting: str = "Средневековое королевство на грани войны с тёмными силами."
    premise: str = "Герой находит древнюю карту, ведущую к забытому храму."
    hero_name: str = "Герой"
    hero_desc: str = "молодой странник, ищущий своё предназначение"
    style: str = "атмосферно, с деталями, среднее по длине повествование"
    rpg_mode: bool = False
    base_stats: dict = field(default_factory=dict)
    moderation: str = "none"  # none | soft | strict

    def to_dict(self):
        return asdict(self)


def from_dict(d):
    if not isinstance(d, dict):
        return StoryConfig()
    defaults = StoryConfig()
    return StoryConfig(
        **{
            f.name: d.get(f.name, getattr(defaults, f.name))
            for f in fields(StoryConfig)
        }
    )


def load_presets():
    if not os.path.exists(PRESETS_FILE):
        return {}
    try:
        with open(PRESETS_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        if not isinstance(data, dict):
            return {}
        return data
    except Exception:
        return {}


def save_preset(name: str, cfg: StoryConfig):
    presets = load_presets()
    presets[name] = cfg.to_dict()
    with open(PRESETS_FILE, "w", encoding="utf-8") as f:
        json.dump(presets, f, ensure_ascii=False, indent=2)


def _valid_provider(provider_id, providers, default):
    if isinstance(provider_id, str) and provider_id in providers:
        return provider_id
    return default


@dataclass
class AppSettings:
    text_provider: str = "gigachat"
    text_key_pool: list = field(default_factory=list)
    # {provider_id: {"base_url": str, "model": str}}
    # Используется только провайдерами с kind == "openai".
    text_endpoints: dict = field(default_factory=dict)
    # --- Голос ---
    auto_speak: bool = False
    tts_rate: int = TTS_RATE_DEFAULT
    tts_voice: str = ""
    # --- Генерация ---
    temperature: float = DEFAULT_AI_TEMPERATURE
    max_tokens: int = DEFAULT_AI_MAX_TOKENS
    top_p: float = DEFAULT_AI_TOP_P
    turn_length: str = DEFAULT_TURN_LENGTH
    # --- UX ---
    theme: str = "light"          # "light" | "dark"
    smart_scroll: bool = True      # не прыгать вниз, если пользователь ушёл вверх

    def to_dict(self):
        return asdict(self)

    @staticmethod
    def from_dict(d):
        if not isinstance(d, dict):
            return AppSettings()

        def _pool(value):
            if isinstance(value, list):
                return [str(v).strip() for v in value if str(v).strip()]
            return []

        def _endpoints(value):
            if not isinstance(value, dict):
                return {}
            result = {}
            for pid, cfg in value.items():
                if not isinstance(cfg, dict):
                    continue
                base_url = str(cfg.get("base_url", "")).strip()
                model = str(cfg.get("model", "")).strip()
                result[str(pid)] = {"base_url": base_url, "model": model}
            return result

        def _int_or(value, default):
            try:
                return int(value)
            except (TypeError, ValueError):
                return default

        def _float_or(value, default, lo, hi):
            try:
                f = float(value)
            except (TypeError, ValueError):
                return default
            return max(lo, min(hi, f))

        turn_length = str(d.get("turn_length", DEFAULT_TURN_LENGTH)).strip()
        if turn_length not in TURN_LENGTHS:
            turn_length = DEFAULT_TURN_LENGTH
        theme = str(d.get("theme", "light")).strip()
        if theme not in THEMES:
            theme = "light"

        return AppSettings(
            text_provider=_valid_provider(
                d.get("text_provider"), TEXT_PROVIDERS, "gigachat"
            ),
            text_key_pool=_pool(d.get("text_key_pool")),
            text_endpoints=_endpoints(d.get("text_endpoints")),
            auto_speak=bool(d.get("auto_speak", False)),
            tts_rate=_int_or(d.get("tts_rate"), TTS_RATE_DEFAULT),
            tts_voice=str(d.get("tts_voice", "")).strip(),
            temperature=_float_or(
                d.get("temperature"), DEFAULT_AI_TEMPERATURE, 0.1, 1.5
            ),
            max_tokens=_int_or(d.get("max_tokens"), DEFAULT_AI_MAX_TOKENS),
            top_p=_float_or(d.get("top_p"), DEFAULT_AI_TOP_P, 0.1, 1.0),
            turn_length=turn_length,
            theme=theme,
            smart_scroll=bool(d.get("smart_scroll", True)),
        )

# ---------------------------------------------------------------------------
# Безопасное хранение пула ключей
# ---------------------------------------------------------------------------

def _save_key_pool_secure(pool: list) -> bool:
    """
    Пытается сохранить пул в системное хранилище (Windows Credential Manager,
    macOS Keychain, Secret Service на Linux).

    Возвращает True при успехе, False при любой ошибке (нет keyring,
    нет backend, отказ в доступе и т.п.). При False вызывающий код должен
    записать ключи в JSON как раньше — это fallback.
    """
    if not _KEYRING_ENABLED:
        return False
    try:
        payload = json.dumps(list(pool or []), ensure_ascii=False)
        _keyring_mod.set_password(KEYRING_SERVICE, KEYRING_POOL_KEY, payload)
        return True
    except Exception:
        return False


def _load_key_pool_secure():
    """
    Возвращает пул ключей из keyring или None, если ничего нет.
    Ошибки keyring не пробрасываются — просто None.
    """
    if not _KEYRING_ENABLED:
        return None
    try:
        data = _keyring_mod.get_password(KEYRING_SERVICE, KEYRING_POOL_KEY)
    except Exception:
        return None
    if not data:
        return None
    try:
        parsed = json.loads(data)
    except Exception:
        return None
    if isinstance(parsed, list):
        return [str(v).strip() for v in parsed if str(v).strip()]
    return None


def _delete_key_pool_secure() -> bool:
    """Удаляет запись из keyring (используется, если пользователь очистил пул)."""
    if not _KEYRING_ENABLED:
        return False
    try:
        _keyring_mod.delete_password(KEYRING_SERVICE, KEYRING_POOL_KEY)
        return True
    except Exception:
        return False

def load_settings() -> AppSettings:
    if not os.path.exists(SETTINGS_FILE):
        settings = AppSettings()
    else:
        try:
            with open(SETTINGS_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            settings = AppSettings.from_dict(data)
        except Exception:
            settings = AppSettings()

    # Ключи из keyring имеют приоритет над тем, что лежит в JSON.
    secure_pool = _load_key_pool_secure()
    if secure_pool is not None:
        settings.text_key_pool = secure_pool

    # Пересохраняем — мигрируем plain-text ключи в keyring при первой
    # возможности; если keyring недоступен, поведение не меняется.
    try:
        save_settings(settings)
    except Exception:
        pass
    return settings


def save_settings(settings: AppSettings):
    """
    Сохраняет настройки в JSON.

    Пул ключей выносится в keyring, если он доступен. В JSON в поле
    text_key_pool при этом пишется пустой список. Если keyring недоступен —
    ключи пишутся в JSON как раньше (совместимость с headless-окружениями).
    """
    payload = settings.to_dict()
    pool = list(settings.text_key_pool or [])

    if pool and _save_key_pool_secure(pool):
        payload["text_key_pool"] = []
    elif not pool and _KEYRING_ENABLED:
        # Пустой пул: подчистим возможную старую запись в keyring,
        # чтобы она не «воскресла» при следующем запуске.
        try:
            _delete_key_pool_secure()
        except Exception:
            pass

    with open(SETTINGS_FILE, "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False, indent=2)

# ---------------------------------------------------------------------------
# Хранилище сохранений игры
# ---------------------------------------------------------------------------

class SaveManager:
    """
    Управляет JSON-сохранениями в ~/.quest_ai/saves/.

    Формат файла:
      {
        "version": 1,
        "saved_at": "2026-01-01T12:00:00",
        "mode": "single|host|client",
        "turn_count": 12,
        "cfg": {...},
        "history": [{"role": ..., "content": ...}, ...],
        "story_summary": "...",
        "story_buffer": "...",       # готовый текст для окна повествования
        "cards": [...],
        "player_name": "Хост",
        "player_state": {...},
        "remote_player_states": {name: {...}},
        "custom_actions": [...],
        "last_ai_actions": [...]
      }
    """

    def __init__(self, saves_dir: str = SAVES_DIR):
        self.saves_dir = saves_dir
        os.makedirs(self.saves_dir, exist_ok=True)

    # -- Публичный API -----------------------------------------------------

    def list_saves(self) -> list:
        """
        Возвращает список метаданных о сохранениях, отсортированный
        по времени модификации (сначала самые свежие).
        """
        items = []
        try:
            names = os.listdir(self.saves_dir)
        except OSError:
            return []

        for name in names:
            if not name.endswith(".json"):
                continue
            path = os.path.join(self.saves_dir, name)
            if not os.path.isfile(path):
                continue
            try:
                mtime = os.path.getmtime(path)
            except OSError:
                mtime = 0.0

            meta = {
                "path": path,
                "name": name,
                "mtime": mtime,
                "title": name[:-5] if name.lower().endswith(".json") else name,
                "turn_count": None,
                "saved_at": None,
            }

            # Читаем метаданные для подписи в меню
            try:
                with open(path, "r", encoding="utf-8") as f:
                    data = json.load(f)
                if isinstance(data, dict):
                    cfg = data.get("cfg") or {}
                    if isinstance(cfg, dict) and cfg.get("title"):
                        meta["title"] = str(cfg["title"])
                    tc = data.get("turn_count")
                    if isinstance(tc, int):
                        meta["turn_count"] = tc
                    meta["saved_at"] = data.get("saved_at")
            except Exception:
                pass

            items.append(meta)

        items.sort(key=lambda m: m["mtime"], reverse=True)
        return items

    def save(self, path: str, state: dict) -> str:
        """
        Атомарно сохраняет состояние в JSON-файл.
        Сначала пишет во временный файл рядом, затем os.replace — это
        защищает от порванных файлов при выключении компьютера.
        """
        payload = dict(state)
        payload["version"] = SAVE_VERSION
        payload["saved_at"] = datetime.now().isoformat(timespec="seconds")

        tmp_path = path + ".tmp"
        try:
            with open(tmp_path, "w", encoding="utf-8") as f:
                json.dump(payload, f, ensure_ascii=False, indent=2)
            os.replace(tmp_path, path)
        except Exception:
            # подчистим временный файл, чтобы не мусорить
            try:
                if os.path.exists(tmp_path):
                    os.remove(tmp_path)
            except OSError:
                pass
            raise
        return path

    def load(self, path: str) -> dict:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        if not isinstance(data, dict):
            raise ValueError("Файл сохранения повреждён: ожидался JSON-объект.")
        return data

    def autosave(self, state: dict) -> str:
        return self.save(AUTOSAVE_FILE, state)

    def delete(self, path: str):
        try:
            os.remove(path)
        except OSError:
            pass

# ---------------------------------------------------------------------------
# Клиент текстового ИИ
# ---------------------------------------------------------------------------

class AIClient:
    def __init__(self, provider: str = "gigachat"):
        if provider not in TEXT_PROVIDERS:
            provider = "gigachat"
        self.provider = provider
        self._client = None
        self._client_provider = None
        self.key_pool = []
        self._pool_index = 0
        # {provider_id: {"base_url": ..., "model": ...}} — задаётся
        # снаружи через set_endpoint_config().
        self.endpoint_config = {}
        # {provider_id: handler} — плагинные провайдеры.
        self.plugin_providers = {}

    def set_plugin_providers(self, providers: dict):
        """Подменяет реестр плагинных провайдеров (вызывается при загрузке/перезагрузке)."""
        self.plugin_providers = dict(providers or {})

    def set_key_pool(self, pool: list):
        self.key_pool = [str(k).strip() for k in (pool or []) if str(k).strip()]
        self._pool_index = 0
        self._client = None
        self._client_provider = None

    def set_endpoint_config(self, config: dict):
        """Сохраняет Base URL / модель для OpenAI-совместимых провайдеров."""
        clean = {}
        if isinstance(config, dict):
            for pid, cfg in config.items():
                if not isinstance(cfg, dict):
                    continue
                clean[str(pid)] = {
                    "base_url": str(cfg.get("base_url", "")).strip(),
                    "model": str(cfg.get("model", "")).strip(),
                }
        self.endpoint_config = clean

    def get_provider_config(self) -> dict:
        """
        Возвращает сведённые настройки активного провайдера:
        данные из TEXT_PROVIDERS + переопределения из endpoint_config.
        """
        info = TEXT_PROVIDERS.get(self.provider, {})
        override = self.endpoint_config.get(self.provider, {})
        base_url = (override.get("base_url") or info.get("base_url") or "").strip()
        model = (override.get("model") or info.get("model") or "").strip()
        return {
            "kind": info.get("kind", "openai"),
            "base_url": base_url,
            "model": model,
            "no_key": bool(info.get("no_key", False)),
            "extra_headers": dict(info.get("extra_headers") or {}),
            "signup_url": info.get("signup_url", ""),
            "label": info.get("label", self.provider),
        }

    def _current_key(self) -> str:
        """
        Берёт ключ из пула (с учётом текущего индекса) или из переменной
        окружения, подобранной под конкретный провайдер.
        """
        if self.key_pool:
            return self.key_pool[self._pool_index % len(self.key_pool)].strip()

        kind = TEXT_PROVIDERS.get(self.provider, {}).get("kind", "")
        if kind == "openai":
            env_names = {
                "openrouter": ["OPENROUTER_API_KEY"],
                "deepseek":   ["DEEPSEEK_API_KEY"],
                "custom":     ["OPENAI_API_KEY"],
            }.get(self.provider, ["OPENAI_API_KEY"])
            for name in env_names:
                v = os.environ.get(name, "").strip()
                if v:
                    return v
        return ""

    def _rotate_key(self):
        if len(self.key_pool) > 1:
            self._pool_index = (self._pool_index + 1) % len(self.key_pool)
        self._client = None
        self._client_provider = None

    def current_key_label(self) -> str:
        if len(self.key_pool) > 1:
            return f"ключ {self._pool_index + 1}/{len(self.key_pool)}"
        return ""

    @staticmethod
    def _looks_like_quota_error(exc: Exception) -> bool:
        text = str(exc).lower()
        markers = (
            "429", "rate limit", "rate_limit", "too many requests",
            "quota", "insufficient", "лимит", "лимиты", "исчерп",
            "недостаточно", "превыш", "forbidden", "403",
        )
        return any(m in text for m in markers)

    @staticmethod
    def _extract_usage(raw) -> dict:
        """
        Универсально вытаскивает prompt/completion/total из usage-объекта
        любого провайдера (GigaChat SDK-объект, YandexGPT, OpenAI-совместимый).
        Возвращает нормализованный dict (пустой, если данных нет).
        """
        if raw is None:
            return {}

        def _get(obj, *keys):
            for k in keys:
                try:
                    if isinstance(obj, dict):
                        v = obj.get(k)
                    else:
                        v = getattr(obj, k, None)
                except Exception:
                    v = None
                if v is not None:
                    return v
            return None

        prompt = _get(raw, "prompt_tokens", "input_tokens", "inputTextTokens")
        completion = _get(raw, "completion_tokens", "output_tokens",
                          "completionTokens")
        total = _get(raw, "total_tokens", "totalTokens")

        result = {}
        for key, val in (("prompt_tokens", prompt),
                         ("completion_tokens", completion),
                         ("total_tokens", total)):
            if val is None:
                continue
            try:
                result[key] = int(val)
            except (TypeError, ValueError):
                pass
        if "total_tokens" not in result \
                and "prompt_tokens" in result \
                and "completion_tokens" in result:
            result["total_tokens"] = (result["prompt_tokens"]
                                      + result["completion_tokens"])
        return result

    def set_provider(self, provider: str):
        if provider not in TEXT_PROVIDERS:
            provider = "gigachat"
        self.provider = provider
        self._client = None
        self._client_provider = None

    def _get_gigachat_client(self):
        if self._client is not None and self._client_provider == "gigachat":
            return self._client
        try:
            from gigachat import GigaChat
        except ImportError:
            raise RuntimeError(
                "Библиотека 'gigachat' не установлена. "
                "Выполните: pip install gigachat"
            )
        if self.key_pool:
            credentials = self.key_pool[self._pool_index % len(self.key_pool)]
        else:
            auth_key = os.environ.get("GIGACHAT_AUTH_KEY", "").strip()
            client_id = os.environ.get("GIGACHAT_CLIENT_ID", "").strip()
            client_secret = os.environ.get("GIGACHAT_CLIENT_SECRET", "").strip()
            if auth_key:
                credentials = auth_key
            elif client_id and client_secret:
                credentials = f"{client_id}:{client_secret}"
            else:
                raise RuntimeError(
                    "Не найден ключ GigaChat. Введите GIGACHAT_AUTH_KEY "
                    "(или пару GIGACHAT_CLIENT_ID + GIGACHAT_CLIENT_SECRET, либо "
                    "пул ключей в окне настройки). "
                    "Получить ключ: https://developers.sber.ru/studio"
                )
        try:
            self._client = GigaChat(
                credentials=credentials,
                verify_ssl_certs=False,
                scope="GIGACHAT_API_PERS",
                base_url="https://api.giga.chat/v1",
            )
        except TypeError:
            self._client = GigaChat(
                credentials=credentials,
                verify_ssl_certs=False,
            )
        self._client_provider = "gigachat"
        return self._client

    def _gigachat_response(self, system_prompt: str, history: list,
                           temperature: float = DEFAULT_AI_TEMPERATURE,
                           max_tokens: int = DEFAULT_AI_MAX_TOKENS,
                           top_p: float = DEFAULT_AI_TOP_P) -> tuple:
        client = self._get_gigachat_client()
        model_name = TEXT_PROVIDERS["gigachat"]["model"]
        messages = [{"role": "system", "content": system_prompt}]
        for h in history:
            role = "assistant" if h.get("role") == "assistant" else "user"
            messages.append({"role": role, "content": h.get("content", "")})
        payload = {"model": model_name, "messages": messages}
        try:
            payload["temperature"] = float(temperature)
            payload["top_p"] = float(top_p)
            payload["max_tokens"] = int(max_tokens)
        except (TypeError, ValueError):
            pass
        response = client.chat(payload)
        try:
            content = response.choices[0].message.content
        except (AttributeError, IndexError, TypeError):
            if isinstance(response, dict):
                content = response["choices"][0]["message"]["content"]
            else:
                raise RuntimeError(f"Неожиданный ответ GigaChat: {response!r}")
        raw_usage = None
        try:
            if isinstance(response, dict):
                raw_usage = response.get("usage")
            else:
                raw_usage = getattr(response, "usage", None)
        except Exception:
            raw_usage = None
        return (content or "").strip(), self._extract_usage(raw_usage)

    def _get_yandex_credentials(self):
        if self.key_pool:
            entry = self.key_pool[self._pool_index % len(self.key_pool)]
            api_key, _, folder_id = entry.rpartition(":")
            if api_key and folder_id:
                return api_key.strip(), folder_id.strip()
            raise RuntimeError(
                "Неверный формат записи в пуле ключей YandexGPT — ожидается "
                "'API_KEY:FOLDER_ID' на строку."
            )
        api_key = os.environ.get("YANDEX_API_KEY", "").strip()
        folder_id = os.environ.get("YANDEX_FOLDER_ID", "").strip()
        if not api_key or not folder_id:
            raise RuntimeError(
                "Не найдены YANDEX_API_KEY и/или YANDEX_FOLDER_ID. "
                "Получите их в Yandex Cloud: "
                "https://yandex.cloud/ru/docs/ai-studio/"
            )
        return api_key, folder_id

    def _yandexgpt_response(self, system_prompt: str, history: list,
                            temperature: float = DEFAULT_AI_TEMPERATURE,
                            max_tokens: int = DEFAULT_AI_MAX_TOKENS,
                            top_p: float = DEFAULT_AI_TOP_P) -> tuple:
        api_key, folder_id = self._get_yandex_credentials()
        model_name = TEXT_PROVIDERS["yandexgpt"]["model"]
        messages = [{"role": "system", "text": system_prompt}]
        for h in history:
            role = "assistant" if h.get("role") == "assistant" else "user"
            messages.append({"role": role, "text": h.get("content", "")})
        url = "https://llm.api.cloud.yandex.net/foundationModels/v1/completion"
        headers = {
            "Authorization": f"Api-Key {api_key}",
            "Content-Type": "application/json",
        }
        body = {
            "modelUri": f"gpt://{folder_id}/{model_name}",
            "completionOptions": {
                "stream": False,
                "temperature": float(temperature),
                "maxTokens": int(max_tokens),
                "topP": float(top_p),
            },
            "messages": messages,
        }
        data = json.dumps(body).encode("utf-8")
        req = urllib.request.Request(url, data=data, headers=headers, method="POST")
        try:
            with urllib.request.urlopen(req, timeout=90) as resp:
                raw = resp.read().decode("utf-8")
        except urllib.error.HTTPError as e:
            err_body = e.read().decode("utf-8", errors="replace")
            raise RuntimeError(f"YandexGPT HTTP {e.code}: {err_body[:500]}")
        except urllib.error.URLError as e:
            raise RuntimeError(f"Ошибка сети при обращении к YandexGPT: {e}")
        parsed = json.loads(raw)
        try:
            text = parsed["result"]["alternatives"][0]["message"]["text"].strip()
        except (KeyError, IndexError, TypeError):
            raise RuntimeError(f"Неожиданный ответ YandexGPT: {parsed}")
        raw_usage = None
        try:
            raw_usage = parsed.get("result", {}).get("usage")
        except Exception:
            raw_usage = None
        return text, self._extract_usage(raw_usage)

    def _openai_compatible_response(self, system_prompt: str, history: list,
                                    config: dict,
                                    temperature: float = DEFAULT_AI_TEMPERATURE,
                                    max_tokens: int = DEFAULT_AI_MAX_TOKENS,
                                    top_p: float = DEFAULT_AI_TOP_P) -> tuple:
        """
        Универсальный вызов /chat/completions для любого OpenAI-совместимого
        сервера: OpenRouter, DeepSeek, Ollama, LM Studio, vLLM, ...
        """
        label = config.get("label") or self.provider
        base_url = (config.get("base_url") or "").rstrip("/")
        model = (config.get("model") or "").strip()

        if not base_url:
            raise RuntimeError(
                f"Не задан Base URL для провайдера «{label}». "
                "Откройте «Настроить историю...» → блок «Провайдер текста» "
                "и заполните поле Base URL."
            )
        if not model:
            raise RuntimeError(
                f"Не задана модель для провайдера «{label}». "
                "Укажите её в настройках истории."
            )

        url = base_url + "/chat/completions"

        headers = {"Content-Type": "application/json"}
        key = self._current_key()
        if key:
            headers["Authorization"] = f"Bearer {key}"
        elif not config.get("no_key"):
            raise RuntimeError(
                f"Не найден API-ключ для провайдера «{label}». "
                f"Введите его в настройках истории"
                + (f" или получите: {config.get('signup_url')}"
                   if config.get("signup_url") else ".")
            )
        for hk, hv in (config.get("extra_headers") or {}).items():
            headers[str(hk)] = str(hv)

        messages = [{"role": "system", "content": system_prompt}]
        for h in history:
            role = "assistant" if h.get("role") == "assistant" else "user"
            messages.append({"role": role, "content": h.get("content", "")})

        body = {
            "model": model,
            "messages": messages,
            "temperature": float(temperature),
            "max_tokens": int(max_tokens),
            "top_p": float(top_p),
            "stream": False,
        }
        data = json.dumps(body, ensure_ascii=False).encode("utf-8")
        req = urllib.request.Request(url, data=data, headers=headers,
                                     method="POST")

        try:
            with urllib.request.urlopen(req, timeout=120) as resp:
                raw = resp.read().decode("utf-8")
        except urllib.error.HTTPError as e:
            err_body = e.read().decode("utf-8", errors="replace")
            raise RuntimeError(f"{label} HTTP {e.code}: {err_body[:500]}")
        except urllib.error.URLError as e:
            hint = ""
            if self.provider == "ollama":
                hint = ("\nПроверьте, что сервер Ollama запущен "
                        "(команда `ollama serve`) и модель загружена "
                        "(например, `ollama pull llama3.1`).")
            raise RuntimeError(
                f"Ошибка сети при обращении к {label}: {e}{hint}"
            )

        try:
            parsed = json.loads(raw)
        except json.JSONDecodeError:
            raise RuntimeError(f"{label} вернул не-JSON: {raw[:300]}")

        # OpenAI-формат
        try:
            text = parsed["choices"][0]["message"]["content"].strip()
        except (KeyError, IndexError, TypeError):
            # Иногда провайдер возвращает ошибку в теле с кодом 200
            err = (parsed.get("error") if isinstance(parsed, dict) else None)
            if err:
                raise RuntimeError(f"{label}: {err}")
            raise RuntimeError(f"Неожиданный ответ {label}: {parsed}")
        raw_usage = parsed.get("usage") if isinstance(parsed, dict) else None
        return text, self._extract_usage(raw_usage)

    def get_response_with_usage(self, system_prompt: str, history: list,
                                temperature: float = DEFAULT_AI_TEMPERATURE,
                                max_tokens: int = DEFAULT_AI_MAX_TOKENS,
                                top_p: float = DEFAULT_AI_TOP_P):
        """
        Возвращает (content: str, usage: dict).
        usage может быть пустым, если провайдер его не вернул.
        """
        # Плагинный провайдер — до всей остальной логики.
        plugin_handler = self.plugin_providers.get(self.provider)
        if plugin_handler is not None:
            result = plugin_handler(
                system_prompt, history, temperature, max_tokens, top_p,
            )
            if isinstance(result, tuple) and len(result) == 2:
                text, usage = result
                return str(text or ""), dict(usage or {})
            return str(result or ""), {}

        config = self.get_provider_config()
        kind = config["kind"]
        attempts = max(1, len(self.key_pool))
        last_err = None
        for _ in range(attempts):
            try:
                if kind == "gigachat":
                    return self._gigachat_response(
                        system_prompt, history, temperature, max_tokens, top_p
                    )
                elif kind == "yandex":
                    return self._yandexgpt_response(
                        system_prompt, history, temperature, max_tokens, top_p
                    )
                elif kind == "openai":
                    return self._openai_compatible_response(
                        system_prompt, history, config,
                        temperature, max_tokens, top_p
                    )
                raise ValueError(f"Неизвестный kind провайдера: {kind}")
            except Exception as e:
                last_err = e
                if len(self.key_pool) > 1 and self._looks_like_quota_error(e):
                    self._rotate_key()
                    continue
                raise
        raise last_err

    def get_response(self, system_prompt: str, history: list,
                     temperature: float = DEFAULT_AI_TEMPERATURE,
                     max_tokens: int = DEFAULT_AI_MAX_TOKENS,
                     top_p: float = DEFAULT_AI_TOP_P) -> str:
        """Обратная совместимость: возвращает только текст."""
        content, _usage = self.get_response_with_usage(
            system_prompt, history, temperature, max_tokens, top_p
        )
        return content

    def summarize_dialogue(self, entries: list, previous_summary: str = "") -> str:
        dialogue_text = "\n".join(
            f"{'Игрок' if e.get('role') == 'user' else 'Гейммастер'}: {e.get('content', '')}"
            for e in entries
        )
        system = (
            "Ты помогаешь вести долгую текстовую ролевую игру и следишь за краткой "
            "памятью сюжета. Тебе даны предыдущее краткое резюме (может быть пустым) "
            "и новый фрагмент диалога. Составь ОБНОВЛЁННОЕ краткое резюме всей "
            "истории целиком (не только нового фрагмента) в 6-10 предложениях от "
            "третьего лица. Сохрани ключевые факты, находки, имена персонажей, "
            "важные решения игрока и текущее положение дел. Не используй теги "
            "[ACTIONS]/[CARD], не добавляй ничего от себя — только пересказывай "
            "уже случившееся."
        )
        user_content = (
            f"Предыдущее резюме:\n{previous_summary or '(пока пусто)'}\n\n"
            f"Новый фрагмент диалога:\n{dialogue_text}"
        )
        return self.get_response(system, [{"role": "user", "content": user_content}])

# ---------------------------------------------------------------------------
# Движок озвучки
# ---------------------------------------------------------------------------

class VoiceEngine:
    """
    Асинхронная озвучка через pyttsx3.

    Работает в отдельном потоке; Tk-поток только кладёт текст в очередь.
    Инициализация pyttsx3 происходит внутри worker-потока — это требование
    библиотеки на Windows (SAPI5 нельзя переиспользовать между потоками).
    """

    def __init__(self, rate: int = TTS_RATE_DEFAULT, voice_id: str = ""):
        self._rate = int(rate) if rate else TTS_RATE_DEFAULT
        self._voice_id = (voice_id or "").strip()
        self._queue = queue.Queue()
        self._stop = threading.Event()
        self._thread = None
        self._available = False
        self._init_error = ""
        self._lock = threading.Lock()
        self._check()

    # -- Публичный API -----------------------------------------------------

    def is_available(self) -> bool:
        return self._available

    def last_error(self) -> str:
        return self._init_error

    def set_rate(self, rate: int):
        try:
            self._rate = int(rate)
        except (TypeError, ValueError):
            pass

    def say(self, text: str):
        """Разбивает текст на куски и кладёт их в очередь озвучки."""
        if not self._available:
            return
        chunks = _split_for_tts(text)
        if not chunks:
            return
        for ch in chunks:
            self._queue.put(ch)
        self._ensure_worker()

    def stop_current(self):
        """Сбрасывает очередь. Текущая фраза доигрывается."""
        while True:
            try:
                self._queue.get_nowait()
            except queue.Empty:
                break

    def shutdown(self):
        self._stop.set()
        try:
            self._queue.put(None)
        except Exception:
            pass
        t = self._thread
        if t and t.is_alive():
            t.join(timeout=1.5)

    def is_speaking(self) -> bool:
        return self._thread is not None and self._thread.is_alive()

    # -- Внутреннее --------------------------------------------------------

    def _check(self):
        ok, msg = _check_tts_available()
        self._available = ok
        self._init_error = msg if not ok else ""

    def _ensure_worker(self):
        with self._lock:
            if self._thread is not None and self._thread.is_alive():
                return
            self._stop.clear()
            self._thread = threading.Thread(
                target=self._worker, daemon=True, name="VoiceEngine"
            )
            self._thread.start()

    def _worker(self):
        # pyttsx3 нужно инициализировать именно в рабочем потоке.
        try:
            import pyttsx3
            engine = pyttsx3.init()
        except Exception as e:
            self._available = False
            self._init_error = f"Ошибка инициализации pyttsx3: {e}"
            return

        # Голос
        if self._voice_id:
            try:
                for v in engine.getProperty("voices") or []:
                    if v.id == self._voice_id or self._voice_id in (v.id or ""):
                        engine.setProperty("voice", v.id)
                        break
            except Exception:
                pass

        while not self._stop.is_set():
            try:
                text = self._queue.get(timeout=0.5)
            except queue.Empty:
                continue
            if text is None:
                break
            try:
                engine.setProperty("rate", int(self._rate))
                engine.say(text)
                engine.runAndWait()
            except Exception:
                # Один плохой кусок — не повод ронять весь поток
                pass

        try:
            engine.stop()
        except Exception:
            pass


# ---------------------------------------------------------------------------
# Мультиплеер
# ---------------------------------------------------------------------------

def _iter_bounded_lines(reader, max_chars: int = MAX_LINE_CHARS):
    """
    Генератор, который читает строки из файлового объекта, но:
      * ограничивает длину каждой строки max_chars символами;
      * если строка длиннее, «съедает» её остаток и переходит к следующей;
      * никогда не уходит в бесконечный рост памяти.

    Заменяет `for line in reader:` там, где данные приходят из сети.
    """
    overlong = False
    while True:
        try:
            line = reader.readline(max_chars)
        except (OSError, ValueError):
            return
        if not line:
            return
        if overlong:
            # Предыдущий кусок был слишком длинным — ждём доедания.
            if line.endswith("\n") or len(line) < max_chars:
                overlong = False
            continue
        if len(line) >= max_chars and not line.endswith("\n"):
            # Начался слишком длинный «пакет» — пропускаем его целиком.
            overlong = True
            continue
        yield line

class GameServer:
    """
    Хост-сервер мультиплеера.

    Возможности:
      * роли (ведущий / игрок / наблюдатель);
      * чат игроков (сообщения не уходят в ИИ);
      * heartbeat: клиенты шлют ping, сервер отвечает pong;
      * приватные действия — флаг private в сообщении action;
      * отключение мёртвых клиентов по таймауту.
    """

    def __init__(self, host_app, port: int, password: str = ""):
        self.host_app = host_app
        self.port = port
        self.password = (password or "").strip()
        self._sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self._sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self._sock.bind(("0.0.0.0", port))
        self._sock.listen(8)
        self._clients = {}       # conn -> name
        self._roles = {}         # conn -> role
        self._last_seen = {}     # conn -> unix timestamp (любое сообщение)
        self._last_active = {}   # conn -> unix timestamp (реальное действие)
        self._lock = threading.Lock()
        self._running = True
        threading.Thread(target=self._accept_loop, daemon=True).start()
        threading.Thread(target=self._watchdog_loop, daemon=True).start()

    # -- Публичный API -----------------------------------------------------

    def broadcast(self, payload: dict):
        with self._lock:
            conns = list(self._clients.keys())
        for conn in conns:
            self._send(conn, payload)

    def send_to(self, name: str, payload: dict):
        with self._lock:
            target = None
            for conn, n in self._clients.items():
                if n == name:
                    target = conn
                    break
        if target is not None:
            self._send(target, payload)

    def player_names(self) -> list:
        with self._lock:
            return list(self._clients.values())

    def player_roles(self) -> dict:
        """Возвращает {name: role} для всех клиентов + хоста."""
        with self._lock:
            mapping = {n: self._roles.get(c, ROLE_PLAYER)
                       for c, n in self._clients.items()}
        mapping[self.host_app.player_name] = ROLE_HOST
        return mapping

    def set_role_by_name(self, name: str, role: str):
        if role not in ROLE_LABELS:
            return
        if name == self.host_app.player_name:
            return  # роль ведущего неизменна
        with self._lock:
            for conn, n in self._clients.items():
                if n == name:
                    self._roles[conn] = role
                    break
            else:
                return
        self.broadcast_roles()

    def broadcast_roles(self):
        mapping = self.player_roles()
        self.broadcast({"type": "roles", "roles": mapping})

    def stop(self):
        self._running = False
        try:
            self._sock.close()
        except OSError:
            pass
        with self._lock:
            conns = list(self._clients.keys())
            self._clients.clear()
            self._roles.clear()
            self._last_seen.clear()
            self._last_active.clear()
        for conn in conns:
            try:
                conn.close()
            except OSError:
                pass

    # -- Приём -------------------------------------------------------------

    def _accept_loop(self):
        while self._running:
            try:
                conn, _addr = self._sock.accept()
            except OSError:
                break
            threading.Thread(target=self._client_loop, args=(conn,),
                             daemon=True).start()

    def _client_loop(self, conn):
        name = None
        try:
            reader = conn.makefile("r", encoding="utf-8")
            for line in _iter_bounded_lines(reader):
                line = line.strip()
                if not line:
                    continue
                try:
                    msg = json.loads(line)
                except json.JSONDecodeError:
                    continue

                now_ts = time.time()
                mtype = msg.get("type")

                # Любое сообщение — обновляет «живость» соединения.
                # Реальные действия (не ping) — обновляют и «активность».
                with self._lock:
                    if conn in self._clients:
                        self._last_seen[conn] = now_ts
                        if mtype != "ping":
                            self._last_active[conn] = now_ts

                if mtype == "join":
                    name = self._handle_join(conn, msg)
                    if name is None:
                        return

                elif mtype == "ping":
                    self._send(conn, {"type": "pong", "t": now_ts})

                elif mtype == "chat" and name:
                    text = (msg.get("text") or "").strip()
                    if text:
                        self._handle_chat(name, text)

                elif mtype == "action" and name:
                    text = (msg.get("text") or "").strip()
                    if text:
                        is_private = bool(msg.get("private", False))
                        self.host_app.result_queue.put(
                            ("remote_action",
                             (name, text, is_private))
                        )

                elif mtype == "player_state" and name:
                    state = msg.get("state") or {}
                    self.host_app.result_queue.put(
                        ("remote_player_state", (name, state))
                    )

        except (OSError, ValueError):
            pass
        finally:
            with self._lock:
                left_name = self._clients.pop(conn, None)
                self._roles.pop(conn, None)
                self._last_seen.pop(conn, None)
                self._last_active.pop(conn, None)
            if left_name:
                self.host_app.result_queue.put(("player_left", left_name))
                self.broadcast_roles()
            try:
                conn.close()
            except OSError:
                pass

    def _handle_join(self, conn, msg):
        if self.password and msg.get("password", "") != self.password:
            self._send(conn, {"type": "system", "text": "Неверный пароль."})
            return None
        name = (msg.get("name") or "Игрок").strip()[:30] or "Игрок"
        with self._lock:
            existing = set(self._clients.values())
            base, i = name, 2
            while name in existing:
                name = f"{base}-{i}"
                i += 1
            now_ts = time.time()
            self._clients[conn] = name
            self._roles[conn] = ROLE_PLAYER
            self._last_seen[conn] = now_ts
            self._last_active[conn] = now_ts
        try:
            self._send(conn, self.host_app.get_sync_snapshot())
            self._send(conn, {"type": "roles", "roles": self.player_roles()})
        except Exception as e:
            self._send(conn, {"type": "system",
                              "text": f"Ошибка синхронизации: {e}"})
        self.host_app.result_queue.put(("player_joined", name))
        self.broadcast_roles()
        return name

    def _handle_chat(self, from_name, text):
        # Рассылаем всем, кроме отправителя: он видит свой текст сразу локально.
        with self._lock:
            conns = [(c, n) for c, n in self._clients.items()
                     if n != from_name]
        for conn, _ in conns:
            self._send(conn, {
                "type": "chat", "from": from_name, "text": text,
            })
        # Хосту — через очередь, чтобы не блокировать сетевой поток.
        self.host_app.result_queue.put(("chat_message", (from_name, text)))

    # -- Watchdog ----------------------------------------------------------

    def _watchdog_loop(self):
        """
        Периодически выпинывает клиентов, которые:
          * давно не присылали НИЧЕГО (включая ping) — heartbeat;
          * давно не совершали реальных действий (только пингуют) — idle.

        Наблюдатели (роль ROLE_OBSERVER) от idle-проверки освобождены:
        они по определению не действуют.
        """
        while self._running:
            time.sleep(HEARTBEAT_INTERVAL_MS / 1000.0)
            if not self._running:
                break
            now = time.time()
            dead = []  # нет никаких сообщений — heartbeat
            idle = []  # только ping, без действий — idle
            with self._lock:
                for conn, ts in self._last_seen.items():
                    if now - ts > HEARTBEAT_TIMEOUT_MS / 1000.0:
                        dead.append(conn)
                        continue
                    # Наблюдателей не проверяем на idle.
                    if self._roles.get(conn) == ROLE_OBSERVER:
                        continue
                    active_ts = self._last_active.get(conn, ts)
                    if now - active_ts > IDLE_TIMEOUT_MS / 1000.0:
                        idle.append((conn, self._clients.get(conn, "?")))

            for conn in dead:
                try:
                    conn.close()
                except OSError:
                    pass

            for conn, name in idle:
                # Аккуратно уведомляем клиента перед разрывом.
                try:
                    self._send(conn, {
                        "type": "system",
                        "text": ("Вы отключены за неактивность "
                                 "(5 минут без действий)."),
                    })
                except Exception:
                    pass
                try:
                    conn.close()
                except OSError:
                    pass
                try:
                    self.host_app.result_queue.put(
                        ("player_left", name)
                    )
                except Exception:
                    pass

    @staticmethod
    def _send(conn, payload: dict):
        try:
            data = (json.dumps(payload, ensure_ascii=False) + "\n").encode("utf-8")
            conn.sendall(data)
        except OSError:
            pass


class ClientNetwork:
    """
    Клиентское соединение с хостом.

    Дополнительно к базовому протоколу:
      * шлёт ping каждые HEARTBEAT_INTERVAL_MS;
      * следит за ответами pong; если pong не пришёл за HEARTBEAT_TIMEOUT_MS —
        вызывает on_disconnect, и MainApp инициирует переподключение.
    """

    def __init__(self, host: str, port: int, name: str, password: str,
                 on_message, on_disconnect):
        self.host = host
        self.port = port
        self.name = name
        self.password = password
        self.sock = socket.create_connection((host, port), timeout=10)
        self._on_message = on_message
        self._on_disconnect = on_disconnect
        self._last_pong = time.time()
        self._alive = True
        self._ping_thread = None
        self._watchdog_thread = None

        self.send({"type": "join", "name": name, "password": password})

        threading.Thread(target=self._read_loop, daemon=True,
                         name="ClientRead").start()
        self._ping_thread = threading.Thread(
            target=self._ping_loop, daemon=True, name="ClientPing"
        )
        self._ping_thread.start()
        self._watchdog_thread = threading.Thread(
            target=self._watchdog_loop, daemon=True, name="ClientWatchdog"
        )
        self._watchdog_thread.start()

    # -- Публичный API -----------------------------------------------------

    def send(self, payload: dict):
        try:
            data = (json.dumps(payload, ensure_ascii=False) + "\n").encode("utf-8")
            self.sock.sendall(data)
        except OSError:
            self._alive = False

    def is_alive(self) -> bool:
        return self._alive

    def send_ping(self):
        self.send({"type": "ping", "t": time.time()})

    def close(self):
        self._alive = False
        try:
            self.sock.close()
        except OSError:
            pass

    # -- Внутренние циклы --------------------------------------------------

    def _ping_loop(self):
        while self._alive:
            time.sleep(HEARTBEAT_INTERVAL_MS / 1000.0)
            if not self._alive:
                break
            self.send_ping()

    def _watchdog_loop(self):
        while self._alive:
            time.sleep(2.0)
            if not self._alive:
                break
            if (time.time() - self._last_pong) > HEARTBEAT_TIMEOUT_MS / 1000.0:
                if self._alive:
                    self._alive = False
                    try:
                        self._on_disconnect()
                    except Exception:
                        pass
                break

    def _read_loop(self):
        try:
            reader = self.sock.makefile("r", encoding="utf-8")
            for line in _iter_bounded_lines(reader):
                line = line.strip()
                if not line:
                    continue
                try:
                    msg = json.loads(line)
                except json.JSONDecodeError:
                    continue
                if isinstance(msg, dict) and msg.get("type") == "pong":
                    self._last_pong = time.time()
                    continue
                self._on_message(msg)
        except OSError:
            pass
        finally:
            was_alive = self._alive
            self._alive = False
            if was_alive:
                try:
                    self._on_disconnect()
                except Exception:
                    pass

# ---------------------------------------------------------------------------
# Хранилище карточек
# ---------------------------------------------------------------------------

class CardStore:
    """
    Хранилище карточек предметов, существ и NPC.

    Поля карточки:
      * name        — обязательное, по нему ищется дубликат (без учёта регистра);
      * type        — "предмет" / "существо";
      * description — текстовое описание;
      * properties  — dict свойств;
      * equip_slot  — слот экипировки (для носимых предметов);
      * status      — "жив"/"мёртв"/"потерян"/"уничтожен"/"неизвестно";
      * attitude    — "союзник"/"нейтрал"/"враг"/"неизвестно";
      * hp          — число или строка;
      * location    — название локации.
    """

    def __init__(self):
        self.cards = []

    # -- Нормализация ------------------------------------------------------

    @staticmethod
    def _normalize(card: dict) -> dict:
        if not isinstance(card, dict):
            return {
                "name": "Без названия",
                "type": "предмет",
                "description": "",
                "properties": {},
            }
        card = dict(card)

        # --- Санитизация строк и вложений ---
        name = _clip_str(card.get("name"), MAX_CARD_NAME_LEN).strip()
        card["name"] = name or "Без названия"

        type_val = _clip_str(card.get("type"), 40).strip().lower()
        card["type"] = type_val or "предмет"

        card["description"] = _clip_str(
            card.get("description"), MAX_CARD_DESC_LEN
        )

        # properties — только плоский dict[str → str/int/float/bool]
        props = card.get("properties")
        if not isinstance(props, dict):
            props = {}
        clean_props = {}
        count = 0
        for k, v in props.items():
            if count >= MAX_CARD_PROPS_COUNT:
                break
            ks = _clip_str(k, 100).strip()
            if not ks:
                continue
            if isinstance(v, (int, float, bool)):
                clean_props[ks] = v
            else:
                clean_props[ks] = _clip_str(v, MAX_CARD_PROP_VALUE_LEN)
            count += 1
        card["properties"] = clean_props

        # Остальные поля — короткие строки.
        for key in ("status", "attitude", "hp",
                    "location", "equip_slot",
                    "character", "goal"):
            if key in card and card[key] is not None:
                limit = 40 if key in ("status", "attitude", "hp",
                                      "location", "equip_slot") else 500
                card[key] = _clip_str(card[key], limit)

        return card

    # -- Поиск -------------------------------------------------------------

    def find(self, name: str):
        """Возвращает карточку по имени (без учёта регистра) или None."""
        if not name:
            return None
        lname = str(name).strip().lower()
        for c in self.cards:
            if str(c.get("name", "")).strip().lower() == lname:
                return c
        return None

    def by_type(self, type_: str) -> list:
        """type_ == None → все; иначе фильтр по полю type."""
        if type_ is None:
            return list(self.cards)
        tl = str(type_).lower()
        return [c for c in self.cards if str(c.get("type", "")).lower() == tl]

    def locations(self) -> list:
        """Отсортированный список всех упомянутых локаций."""
        locs = set()
        for c in self.cards:
            loc = c.get("location")
            if loc:
                locs.add(str(loc))
        return sorted(locs)

    # -- Добавление / обновление ------------------------------------------

    def add(self, card: dict):
        """
        Добавляет карточку, только если карточки с таким именем ещё нет.
        Иначе возвращает None (для обратной совместимости).
        """
        card = self._normalize(card)
        if self.find(card["name"]) is not None:
            return None
        self.cards.append(card)
        return card

    def update_or_add(self, card: dict):
        """
        Если карточка с таким именем уже есть — обновляет её:
          * properties мержатся (новые значения перезаписывают старые);
          * остальные поля (type, description, status, attitude, hp,
            location, equip_slot) перезаписываются, если пришли непустыми.

        Возвращает кортеж (card, action), где action ∈ {"added", "updated"}.
        """
        card = self._normalize(card)
        existing = self.find(card["name"])
        if existing is None:
            self.cards.append(card)
            return card, "added"

        # Мержим properties
        old_props = dict(existing.get("properties") or {})
        new_props = dict(card.get("properties") or {})
        old_props.update(new_props)
        existing["properties"] = old_props

        # Обновляем скалярные поля, если пришли непустые
        for key in ("type", "description", "status", "attitude",
                    "hp", "location", "equip_slot",
                    "character", "goal"):
            new_val = card.get(key)
            if new_val not in (None, "", [], {}):
                existing[key] = new_val

        return existing, "updated"

    # -- Удаление ----------------------------------------------------------

    def remove(self, card):
        try:
            self.cards.remove(card)
        except ValueError:
            pass

    # -- Экспорт -----------------------------------------------------------

    @staticmethod
    def _slug(name: str) -> str:
        """Превращает имя карточки в GitHub-совместимый якорь."""
        s = str(name).lower().strip()
        s = re.sub(r"[^\w\s\-]", "", s, flags=re.UNICODE)
        s = re.sub(r"\s+", "-", s)
        return s or "card"

    @staticmethod
    def _write_card_body(lines, c):
        meta = []
        if c.get("status"):
            meta.append(f"статус: **{c['status']}**")
        if c.get("attitude"):
            meta.append(f"отношение: {c['attitude']}")
        if c.get("hp") not in (None, ""):
            meta.append(f"HP: {c['hp']}")
        if c.get("location"):
            meta.append(f"локация: {c['location']}")
        if c.get("equip_slot"):
            meta.append(f"слот: {c['equip_slot']}")
        if meta:
            lines.append("_" + "; ".join(meta) + "_\n")

        if c.get("description"):
            lines.append(str(c["description"]) + "\n")

        props = c.get("properties") or {}
        if props:
            lines.append("**Свойства:**\n")
            for k, v in props.items():
                lines.append(f"- **{k}**: {v}")
            lines.append("")

    def export_markdown(self, path: str):
        """
        Экспортирует весь мир в один Markdown-файл:
          * оглавление со ссылками;
          * раздел «Предметы»;
          * раздел «Существа и NPC»;
          * раздел «Прочее»;
          * внутри раздела — список ссылок и подробные подразделы.
        """
        items = [c for c in self.cards
                 if str(c.get("type", "")).lower() == "предмет"]
        creatures = [c for c in self.cards
                     if str(c.get("type", "")).lower() == "существо"]
        others = [c for c in self.cards if c not in items and c not in creatures]

        lines = []
        lines.append("# Мир истории — карточки\n")

        # --- Оглавление ---
        lines.append("## Содержание\n")
        if items:
            lines.append(f"- [Предметы](#предметы) — {len(items)}")
        if creatures:
            lines.append(
                f"- [Существа и NPC](#существа-и-npc) — {len(creatures)}"
            )
        if others:
            lines.append(f"- [Прочее](#прочее) — {len(others)}")
        lines.append("")

        def _write_group(title, group, anchor):
            if not group:
                return
            lines.append(f"## {title}\n")
            for c in group:
                lines.append(f"- [{c['name']}](#{self._slug(c['name'])})")
            lines.append("")
            for c in group:
                lines.append(f"### {c['name']}\n")
                self._write_card_body(lines, c)
                lines.append("")

        _write_group("Предметы", items, "предметы")
        _write_group("Существа и NPC", creatures, "существа-и-npc")
        _write_group("Прочее", others, "прочее")

        with open(path, "w", encoding="utf-8") as f:
            f.write("\n".join(lines))

    def export_json(self, path: str):
        with open(path, "w", encoding="utf-8") as f:
            json.dump(self.cards, f, ensure_ascii=False, indent=2)

# ---------------------------------------------------------------------------
# Журнал квестов
# ---------------------------------------------------------------------------

class QuestStore:
    """
    Хранилище квестов.

    Поля квеста:
      * name        — обязательное, уникальный ключ (без учёта регистра);
      * description — краткое описание цели;
      * status      — "active" / "done" / "failed";
      * created_at  — номер хода, когда квест появился;
      * updated_at  — номер хода последнего изменения.
    """

    def __init__(self):
        self.quests = []

    # -- Нормализация ------------------------------------------------------

    @staticmethod
    def _normalize(quest: dict) -> dict:
        q = dict(quest)
        q.setdefault("name", "Без названия")
        q.setdefault("description", "")
        status = str(q.get("status", "active")).strip().lower()
        q["status"] = QUEST_STATUS_ALIASES.get(status, "active")
        if q["status"] not in QUEST_STATUSES:
            q["status"] = "active"
        q.setdefault("created_at", 0)
        q.setdefault("updated_at", 0)
        return q

    # -- Поиск -------------------------------------------------------------

    def find(self, name: str):
        if not name:
            return None
        lname = str(name).strip().lower()
        for q in self.quests:
            if str(q.get("name", "")).strip().lower() == lname:
                return q
        return None

    def by_status(self, status: str) -> list:
        if status is None:
            return list(self.quests)
        return [q for q in self.quests if q.get("status") == status]

    def active(self) -> list:
        return self.by_status("active")

    # -- Добавление / обновление ------------------------------------------

    def add(self, quest: dict, turn_count: int = 0):
        q = self._normalize(quest)
        if self.find(q["name"]) is not None:
            return None
        q["created_at"] = int(turn_count)
        q["updated_at"] = int(turn_count)
        self.quests.append(q)
        return q

    def update_or_add(self, quest: dict, turn_count: int = 0):
        """
        Возвращает (quest, action), где action ∈ {"added", "updated"}.
        Обновляет только непустые поля; статус перезаписывается, если пришёл.
        """
        quest = self._normalize(quest)
        existing = self.find(quest["name"])
        if existing is None:
            quest["created_at"] = int(turn_count)
            quest["updated_at"] = int(turn_count)
            self.quests.append(quest)
            return quest, "added"

        if quest.get("description"):
            existing["description"] = quest["description"]
        # Статус — специально: даже если ИИ прислал active повторно,
        # это может быть «возобновление» квеста, поэтому перезаписываем
        # только при смене фактического значения.
        new_status = quest.get("status")
        if new_status and new_status != existing.get("status"):
            existing["status"] = new_status
        existing["updated_at"] = int(turn_count)
        return existing, "updated"

    def set_status(self, quest, status: str):
        if status not in QUEST_STATUSES:
            return
        quest["status"] = status

    def remove(self, quest):
        try:
            self.quests.remove(quest)
        except ValueError:
            pass

    # -- Экспорт -----------------------------------------------------------

    def export_markdown(self, path: str):
        lines = ["# Журнал квестов\n"]
        groups = [
            ("Активные", self.by_status("active")),
            ("Выполненные", self.by_status("done")),
            ("Проваленные", self.by_status("failed")),
        ]
        if not any(g for _, g in groups):
            lines.append("_Пока ни одного квеста не записано._\n")
        for title, group in groups:
            if not group:
                continue
            lines.append(f"## {title} ({len(group)})\n")
            for q in group:
                lines.append(f"### {q['name']}\n")
                if q.get("description"):
                    lines.append(f"{q['description']}\n")
                meta = []
                if q.get("created_at"):
                    meta.append(f"открыт на ходу {q['created_at']}")
                if q.get("updated_at") and q["updated_at"] != q.get("created_at"):
                    meta.append(f"обновлён на ходу {q['updated_at']}")
                if meta:
                    lines.append("_" + "; ".join(meta) + "_\n")
                lines.append("")
        with open(path, "w", encoding="utf-8") as f:
            f.write("\n".join(lines))

    def export_json(self, path: str):
        with open(path, "w", encoding="utf-8") as f:
            json.dump(self.quests, f, ensure_ascii=False, indent=2)

# ---------------------------------------------------------------------------
# Хранилище локаций
# ---------------------------------------------------------------------------

class LocationStore:
    """
    Хранилище локаций и связей между ними.

    Поля локации:
      * name        — обязательное, уникальное (без учёта регистра);
      * description — короткое описание;
      * connections — список имён соседних локаций;
      * discovered  — True, если герой уже был здесь; False — «серая» точка
                      на карте (упомянута, но не посещена).
    """

    def __init__(self):
        self.locations = []

    # -- Нормализация ------------------------------------------------------

    @staticmethod
    def _normalize(loc: dict, discovered: bool = None) -> dict:
        loc = dict(loc)
        loc.pop("current", None)  # транзиентный флаг, в хранилище не нужен
        # Коэрсим в str: "name"/"description" приходят из JSON, который
        # генерирует ИИ, и при сбое формата могут оказаться не строкой
        # (например, списком) — без этого .strip() ниже упал бы с AttributeError.
        loc["name"] = str(loc.get("name") or "Без названия").strip() or "Без названия"
        loc["description"] = str(loc.get("description") or "")
        conns = loc.get("connections") or []
        if not isinstance(conns, list):
            conns = []
        lname = loc["name"].strip().lower()
        seen = set()
        clean = []
        for c in conns:
            cs = str(c).strip()
            if not cs:
                continue
            cl = cs.lower()
            if cl == lname or cl in seen:
                continue
            seen.add(cl)
            clean.append(cs)
        loc["connections"] = clean
        if discovered is not None:
            loc["discovered"] = bool(discovered)
        else:
            loc.setdefault("discovered", True)
        return loc

    # -- Поиск -------------------------------------------------------------

    def find(self, name: str):
        if not name:
            return None
        lname = str(name).strip().lower()
        for loc in self.locations:
            if str(loc.get("name", "")).strip().lower() == lname:
                return loc
        return None

    def names(self) -> list:
        return [loc["name"] for loc in self.locations]

    # -- Добавление / обновление ------------------------------------------

    def add(self, loc: dict, discovered: bool = None):
        loc = self._normalize(loc, discovered=discovered)
        if self.find(loc["name"]) is not None:
            return None
        self.locations.append(loc)
        return loc

    def update_or_add(self, loc: dict, discovered: bool = None):
        """
        Возвращает (loc, action), где action ∈ {"added", "updated"}.
        Обновляет только непустые поля; связи — объединяет.
        Попутно создаёт «серые» заглушки для незнакомых соседей.
        """
        loc = self._normalize(loc, discovered=discovered)
        existing = self.find(loc["name"])

        if existing is None:
            self.locations.append(loc)
            self._ensure_neighbors(loc)
            return loc, "added"

        if loc.get("description"):
            existing["description"] = loc["description"]

        # Объединяем связи
        old = set(str(c).strip().lower()
                  for c in existing.get("connections", []))
        for c in loc.get("connections", []):
            cl = str(c).strip().lower()
            if cl and cl not in old:
                existing.setdefault("connections", []).append(str(c).strip())
                old.add(cl)

        # Если пришло с discovered=True — отмечаем посещённой.
        if discovered is True:
            existing["discovered"] = True

        self._ensure_neighbors(existing)
        return existing, "updated"

    def _ensure_neighbors(self, loc: dict):
        """Создаёт заглушки для соседей, которых ещё нет в хранилище."""
        for cname in loc.get("connections", []):
            if self.find(cname) is None:
                stub = self._normalize({
                    "name": cname,
                    "description": "",
                    "connections": [loc["name"]],
                }, discovered=False)
                self.locations.append(stub)

    def mark_discovered(self, name: str):
        loc = self.find(name)
        if loc is not None:
            loc["discovered"] = True
        return loc

    def remove(self, loc: dict):
        try:
            self.locations.remove(loc)
        except ValueError:
            return
        # Удаляем исходящие связи на него
        lname = str(loc.get("name", "")).strip().lower()
        for other in self.locations:
            conns = other.get("connections") or []
            other["connections"] = [
                c for c in conns
                if str(c).strip().lower() != lname
            ]

    # -- Экспорт -----------------------------------------------------------

    def export_markdown(self, path: str):
        lines = ["# Карта мира\n"]
        if not self.locations:
            lines.append("_Пока ни одной локации не обнаружено._\n")
        else:
            for loc in self.locations:
                status = "✓" if loc.get("discovered", True) else "?"
                lines.append(f"## {status} {loc['name']}\n")
                if loc.get("description"):
                    lines.append(f"{loc['description']}\n")
                conns = loc.get("connections") or []
                if conns:
                    lines.append("**Связано с:** " + ", ".join(conns) + "\n")
                lines.append("")
        with open(path, "w", encoding="utf-8") as f:
            f.write("\n".join(lines))

    def export_json(self, path: str):
        with open(path, "w", encoding="utf-8") as f:
            json.dump(self.locations, f, ensure_ascii=False, indent=2)


# ---------------------------------------------------------------------------
# Состояние игрока
# ---------------------------------------------------------------------------

class PlayerState:
    def __init__(self, name: str = "Герой", stats: dict = None):
        self.name = name
        self.inventory = []
        self.equipped = {}
        # Базовые характеристики (без учёта экипировки)
        base = dict(DEFAULT_STATS)
        if isinstance(stats, dict):
            for k, v in stats.items():
                try:
                    base[str(k)] = int(v)
                except (TypeError, ValueError):
                    continue
        self.stats = base

    def to_dict(self):
        return {
            "name": self.name,
            "inventory": [dict(it) for it in self.inventory],
            "equipped": {k: dict(v) for k, v in self.equipped.items()},
            "stats": dict(self.stats),
        }

    @staticmethod
    def from_dict(d):
        if not isinstance(d, dict):
            return PlayerState()
        ps = PlayerState(str(d.get("name") or "Герой"))
        if isinstance(d.get("inventory"), list):
            ps.inventory = [dict(x) for x in d["inventory"] if isinstance(x, dict)]
        if isinstance(d.get("equipped"), dict):
            ps.equipped = {
                k: dict(v) for k, v in d["equipped"].items()
                if k in EQUIPMENT_SLOT_IDS and isinstance(v, dict)
            }
        if isinstance(d.get("stats"), dict):
            merged = dict(DEFAULT_STATS)
            for k, v in d["stats"].items():
                try:
                    merged[str(k)] = int(v)
                except (TypeError, ValueError):
                    continue
            ps.stats = merged
        return ps

    # -- Характеристики ---------------------------------------------------

    @staticmethod
    def _extract_bonus(value):
        """Извлекает целое из '2', '+2', 'урон +3', 5 и т.п."""
        if isinstance(value, bool):
            return None
        if isinstance(value, (int, float)):
            return int(value)
        if isinstance(value, str):
            m = re.search(r"[-+]?\d+", value)
            if m:
                try:
                    return int(m.group(0))
                except ValueError:
                    return None
        return None

    def get_effective_stats(self) -> dict:
        """
        Базовые характеристики + бонусы от экипировки.
        Бонус учитывается, если имя характеристики встречается
        в ключе свойства (без учёта регистра).
        """
        stats = dict(self.stats or DEFAULT_STATS)
        for item in self.equipped.values():
            if not isinstance(item, dict):
                continue
            props = item.get("properties") or {}
            if not isinstance(props, dict):
                continue
            for key, value in props.items():
                bonus = self._extract_bonus(value)
                if bonus is None:
                    continue
                key_l = str(key).strip().lower()
                matched = False
                for stat_name in stats.keys():
                    if str(stat_name).strip().lower() in key_l:
                        stats[stat_name] = stats.get(stat_name, 0) + bonus
                        matched = True
                        break
                if matched:
                    continue
                # Запасной матч по стандартным именам
                for stat_name in STAT_NAMES:
                    if stat_name in key_l and stat_name not in stats:
                        stats[stat_name] = bonus
                        break
        return stats

    def equipment_bonus(self, stat_name: str) -> int:
        """Сколько бонусов даёт экипировка по конкретной характеристике."""
        base = int(self.stats.get(stat_name, 0))
        eff = int(self.get_effective_stats().get(stat_name, 0))
        return eff - base

    # -- Инвентарь ---------------------------------------------------------

    def add_item(self, item: dict):
        item = dict(item)
        item.setdefault("name", "Без названия")
        item.setdefault("type", "предмет")
        item.setdefault("description", "")
        item.setdefault("properties", {})
        self.inventory.append(item)
        return item

    @staticmethod
    def guess_slot(item: dict):
        # ... (без изменений — оставить как есть)
        if not isinstance(item, dict):
            return None
        explicit = item.get("equip_slot")
        if isinstance(explicit, str) and explicit in EQUIPMENT_SLOT_IDS:
            return explicit
        props = item.get("properties") or {}
        if isinstance(props, dict):
            for k, v in props.items():
                kl = str(k).lower()
                if "слот" in kl or "slot" in kl:
                    vs = str(v).strip().lower()
                    if vs in EQUIPMENT_SLOT_IDS:
                        return vs
        name = (item.get("name") or "").lower()
        checks = [
            ("weapon", ("меч", "топор", "копь", "лук", "кинжал",
                        "посох", "молот", "клинок", "палиц", "арбалет",
                        "sword", "axe", "bow", "dagger", "staff")),
            ("shield", ("щит", "shield")),
            ("head", ("шлем", "каск", "шапк", "корон", "венц",
                      "helmet", "crown")),
            ("body", ("брон", "доспех", "кольчуг", "кирас", "рубах",
                      "armor", "cuirass")),
            ("hands", ("перчат", "рукавиц", "glove", "gauntlet")),
            ("legs", ("штаны", "порт", "брюк", "понож", "legs", "pants")),
            ("feet", ("сапог", "ботин", "туфл", "лапт", "boots", "shoes")),
            ("belt", ("пояс", "ремень", "belt")),
            ("amulet", ("амулет", "ожерел", "медальон", "amulet",
                        "necklace", "pendant")),
            ("ring", ("кольц", "перст", "ring")),
        ]
        for slot, markers in checks:
            if any(m in name for m in markers):
                return slot
        return None

    # ... equip / equip_into_slot / unequip без изменений
    def equip(self, inv_index: int):
        if not (0 <= inv_index < len(self.inventory)):
            return None, "Неверный индекс предмета."
        item = self.inventory[inv_index]
        slot = self.guess_slot(item)
        if not slot:
            return None, (
                "Не удалось определить слот. Укажите поле equip_slot "
                "или свойство «слот» со значением из списка "
                + ", ".join(EQUIPMENT_SLOT_IDS) + "."
            )
        prev = self.equipped.get(slot)
        self.equipped[slot] = item
        del self.inventory[inv_index]
        if prev is not None:
            self.inventory.append(prev)
        return slot, None

    def equip_into_slot(self, inv_index: int, slot: str):
        if slot not in EQUIPMENT_SLOT_IDS:
            return "Неизвестный слот."
        if not (0 <= inv_index < len(self.inventory)):
            return "Неверный индекс предмета."
        item = self.inventory[inv_index]
        prev = self.equipped.get(slot)
        self.equipped[slot] = item
        del self.inventory[inv_index]
        if prev is not None:
            self.inventory.append(prev)
        return None

    def unequip(self, slot: str):
        item = self.equipped.pop(slot, None)
        if item is not None:
            self.inventory.append(item)
        return item


# ---------------------------------------------------------------------------
# Редактор предмета
# ---------------------------------------------------------------------------

class ItemEditor(tk.Toplevel):
    def __init__(self, master, item: dict, on_save=None):
        super().__init__(master)
        self.title("Предмет")
        self.geometry("520x520")
        self.transient(master)
        self.grab_set()
        self.item = dict(item)
        self._on_save = on_save

        frm = ttk.Frame(self)
        frm.pack(fill="both", expand=True, padx=10, pady=10)

        ttk.Label(frm, text="Название:").pack(anchor="w")
        self.name_var = tk.StringVar(value=self.item.get("name", ""))
        ttk.Entry(frm, textvariable=self.name_var).pack(fill="x")

        ttk.Label(frm, text="Тип (предмет/существо):").pack(anchor="w", pady=(6, 0))
        self.type_var = tk.StringVar(value=self.item.get("type", "предмет"))
        ttk.Combobox(frm, textvariable=self.type_var,
                     values=["предмет", "существо"],
                     state="readonly").pack(fill="x")

        ttk.Label(frm, text="Слот экипировки (если носимое):").pack(anchor="w", pady=(6, 0))
        slot_ids = ["(нет)"] + [sid for sid, _ in EQUIPMENT_SLOTS]
        cur_slot = self.item.get("equip_slot") or "(нет)"
        if cur_slot not in slot_ids:
            cur_slot = "(нет)"
        self.slot_var = tk.StringVar(value=cur_slot)
        ttk.Combobox(frm, textvariable=self.slot_var, values=slot_ids,
                     state="readonly").pack(fill="x")

        ttk.Label(frm, text="Описание:").pack(anchor="w", pady=(6, 0))
        self.desc_text = tk.Text(frm, height=5, wrap="word")
        self.desc_text.insert("1.0", self.item.get("description", ""))
        self.desc_text.pack(fill="x")

        ttk.Label(frm, text="Свойства (по строке «ключ: значение»):").pack(anchor="w", pady=(6, 0))
        self.props_text = tk.Text(frm, height=6, wrap="word")
        props = self.item.get("properties") or {}
        if isinstance(props, dict):
            for k, v in props.items():
                self.props_text.insert("end", f"{k}: {v}\n")
        self.props_text.pack(fill="x")

        btns = ttk.Frame(frm)
        btns.pack(fill="x", pady=10)
        ttk.Button(btns, text="Сохранить", command=self._save).pack(side="right")
        ttk.Button(btns, text="Отмена", command=self.destroy).pack(side="right", padx=6)

    def _save(self):
        name = self.name_var.get().strip() or "Без названия"
        self.item["name"] = name
        self.item["type"] = self.type_var.get().strip() or "предмет"
        if self.slot_var.get() != "(нет)":
            self.item["equip_slot"] = self.slot_var.get()
        else:
            self.item.pop("equip_slot", None)
        self.item["description"] = self.desc_text.get("1.0", "end").strip()
        props = {}
        for line in self.props_text.get("1.0", "end").splitlines():
            line = line.strip()
            if not line or ":" not in line:
                continue
            k, _, v = line.partition(":")
            k, v = k.strip(), v.strip()
            if k:
                props[k] = v
        self.item["properties"] = props
        self.destroy()
        if self._on_save:
            self._on_save(self.item)


# ---------------------------------------------------------------------------
# Окно настройки истории
# ---------------------------------------------------------------------------

class SetupDialog(tk.Toplevel):
    def __init__(self, master, cfg: StoryConfig, settings: AppSettings, on_done):
        super().__init__(master)
        self.title("Настройка истории")
        self.geometry("680x720")
        self.minsize(600, 540)
        self.on_done = on_done
        self.cfg = cfg
        self.settings = settings
        self.grab_set()

        self._text_pools = {}
        self._text_base_urls = {}
        self._text_models = {}
        self._last_text_provider = None

        outer = ttk.Frame(self)
        outer.pack(fill="both", expand=True)

        canvas = tk.Canvas(outer, highlightthickness=0)
        scrollbar = ttk.Scrollbar(outer, orient="vertical", command=canvas.yview)
        self.inner = ttk.Frame(canvas)
        self.inner.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all")),
        )
        canvas.create_window((0, 0), window=self.inner, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")

        def _on_mousewheel(event):
            try:
                if canvas.winfo_exists():
                    canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
            except tk.TclError:
                pass

        def _bind_wheel(_event=None):
            self.bind_all("<MouseWheel>", _on_mousewheel)

        def _unbind_wheel(_event=None):
            try:
                self.unbind_all("<MouseWheel>")
            except tk.TclError:
                pass

        # Активируем прокрутку только когда курсор внутри окна настройки,
        # и снимаем привязку, когда курсор ушёл — это предотвращает
        # обращения к уже уничтоженному canvas после закрытия окна.
        self.bind("<Enter>", _bind_wheel)
        self.bind("<Leave>", _unbind_wheel)

        pad = {"padx": 10, "pady": 4}

        preset_frame = ttk.LabelFrame(self.inner, text="Готовые истории (пресеты)")
        preset_frame.pack(fill="x", **pad)
        self.preset_var = tk.StringVar()
        self.preset_box = ttk.Combobox(
            preset_frame, textvariable=self.preset_var, state="readonly"
        )
        self._reload_presets()
        self.preset_box.pack(side="left", fill="x", expand=True, padx=6, pady=6)
        ttk.Button(preset_frame, text="Загрузить", command=self._load_preset).pack(
            side="left", padx=4
        )
        ttk.Button(
            preset_frame, text="Сохранить как...", command=self._save_preset_as
        ).pack(side="left", padx=4)

        form = ttk.LabelFrame(self.inner, text="Параметры истории")
        form.pack(fill="both", expand=True, **pad)

        self.vars = {}
        fields = [
            ("title", "Название истории", 1),
            ("genre", "Жанр / тон", 1),
            ("setting", "Мир и сеттинг", 4),
            ("premise", "Завязка сюжета", 4),
            ("hero_name", "Имя героя", 1),
            ("hero_desc", "Описание героя", 3),
            ("style", "Стиль повествования", 2),
        ]
        for key, label, height in fields:
            ttk.Label(form, text=label + ":").pack(anchor="w", padx=6)
            if height == 1:
                var = tk.StringVar(value=getattr(cfg, key))
                entry = ttk.Entry(form, textvariable=var)
                entry.pack(fill="x", padx=6, pady=(0, 6))
                self.vars[key] = var
            else:
                txt = tk.Text(form, height=height, wrap="word")
                txt.insert("1.0", getattr(cfg, key))
                txt.pack(fill="x", padx=6, pady=(0, 6))
                self.vars[key] = txt

        style_preset_frame = ttk.LabelFrame(
            self.inner, text="Быстрые стилевые пресеты"
        )
        style_preset_frame.pack(fill="x", **pad)

        style_hint = ttk.Label(
            style_preset_frame,
            text="Нажмите — заменит поле «Стиль повествования» выше.",
            foreground="#555", wraplength=600, justify="left",
        )
        style_hint.pack(anchor="w", padx=6, pady=(4, 2))

        style_btn_row = ttk.Frame(style_preset_frame)
        style_btn_row.pack(fill="x", padx=6, pady=(0, 6))

        def _apply_style_preset(text):
            widget = self.vars.get("style")
            if widget is None:
                return
            if isinstance(widget, tk.StringVar):
                widget.set(text)
            else:
                widget.delete("1.0", "end")
                widget.insert("1.0", text)

        row_count = 0
        for label, text in STYLE_PRESETS.items():
            ttk.Button(
                style_btn_row, text=label,
                command=lambda t=text: _apply_style_preset(t),
            ).pack(side="left", padx=(0, 4), pady=2)
            row_count += 1
            if row_count % 3 == 0:
                style_btn_row = ttk.Frame(style_preset_frame)
                style_btn_row.pack(fill="x", padx=6, pady=(0, 2))

        mod_frame = ttk.LabelFrame(self.inner, text="Модерация контента")
        mod_frame.pack(fill="x", **pad)

        self.moderation_var = tk.StringVar(
            value=getattr(cfg, "moderation", "none") or "none"
        )
        mod_labels = [
            ("none", "Без ограничений — ведущий свободен"),
            ("soft", "Мягкая — без натурализма и откровенных сцен"),
            ("strict", "Жёсткая — без насилия и эротики"),
        ]
        for val, lab in mod_labels:
            ttk.Radiobutton(
                mod_frame, text=lab, value=val,
                variable=self.moderation_var,
            ).pack(anchor="w", padx=6, pady=(4 if val == "none" else 0, 2))

        gen_frame = ttk.LabelFrame(self.inner, text="Генерация (параметры ИИ)")
        gen_frame.pack(fill="x", **pad)

        # Профили-кнопки
        profile_row = ttk.Frame(gen_frame)
        profile_row.pack(fill="x", padx=6, pady=(6, 4))
        ttk.Label(profile_row, text="Быстрый профиль:",
                  foreground="#555").pack(side="left", padx=(0, 6))

        self.temperature_var = tk.DoubleVar(
            value=float(getattr(settings, "temperature", DEFAULT_AI_TEMPERATURE))
        )
        self.max_tokens_var = tk.IntVar(
            value=int(getattr(settings, "max_tokens", DEFAULT_AI_MAX_TOKENS))
        )
        self.top_p_var = tk.DoubleVar(
            value=float(getattr(settings, "top_p", DEFAULT_AI_TOP_P))
        )

        def _apply_profile(profile):
            self.temperature_var.set(float(profile["temperature"]))
            self.top_p_var.set(float(profile["top_p"]))

        for label, prof in GENERATION_PROFILES.items():
            ttk.Button(
                profile_row, text=label,
                command=partial(_apply_profile, prof),
            ).pack(side="left", padx=(0, 4))

        # Temperature
        temp_row = ttk.Frame(gen_frame)
        temp_row.pack(fill="x", padx=6, pady=(2, 0))
        ttk.Label(temp_row, text="Temperature (креативность):",
                  width=30, anchor="w").pack(side="left")
        self.temp_lbl = ttk.Label(
            temp_row, text=f"{self.temperature_var.get():.2f}", width=6,
            anchor="e",
        )
        self.temp_lbl.pack(side="right")
        temp_scale = ttk.Scale(
            temp_row, from_=0.1, to=1.2, orient="horizontal",
            variable=self.temperature_var,
            command=lambda v: self.temp_lbl.configure(
                text=f"{float(v):.2f}"
            ),
        )
        temp_scale.pack(side="left", fill="x", expand=True, padx=(4, 4))
        ttk.Label(
            gen_frame,
            text="  0.1 — почти канон, 0.7 — сбалансированно, "
                 "1.2 — максимально свободно",
            foreground="#777",
        ).pack(anchor="w", padx=6)

        # Top-p
        top_p_row = ttk.Frame(gen_frame)
        top_p_row.pack(fill="x", padx=6, pady=(6, 0))
        ttk.Label(top_p_row, text="Top-P (разнообразие словаря):",
                  width=30, anchor="w").pack(side="left")
        self.top_p_lbl = ttk.Label(
            top_p_row, text=f"{self.top_p_var.get():.2f}", width=6,
            anchor="e",
        )
        self.top_p_lbl.pack(side="right")
        top_p_scale = ttk.Scale(
            top_p_row, from_=0.1, to=1.0, orient="horizontal",
            variable=self.top_p_var,
            command=lambda v: self.top_p_lbl.configure(
                text=f"{float(v):.2f}"
            ),
        )
        top_p_scale.pack(side="left", fill="x", expand=True, padx=(4, 4))
        ttk.Label(
            gen_frame,
            text="  0.9–0.95 — обычно оптимально; ниже — модель "
                 "осторожнее выбирает слова",
            foreground="#777",
        ).pack(anchor="w", padx=6)

        # max_tokens
        tokens_row = ttk.Frame(gen_frame)
        tokens_row.pack(fill="x", padx=6, pady=(6, 2))
        ttk.Label(tokens_row, text="Max tokens (длина ответа, лимит):",
                  width=30, anchor="w").pack(side="left")
        self.tokens_lbl = ttk.Label(
            tokens_row, text=str(self.max_tokens_var.get()),
            width=6, anchor="e",
        )
        self.tokens_lbl.pack(side="right")
        tokens_scale = ttk.Scale(
            tokens_row, from_=200, to=4000, orient="horizontal",
            variable=self.max_tokens_var,
            command=lambda v: self.tokens_lbl.configure(
                text=str(int(float(v)))
            ),
        )
        tokens_scale.pack(side="left", fill="x", expand=True, padx=(4, 4))

        # Длина хода
        length_row = ttk.Frame(gen_frame)
        length_row.pack(fill="x", padx=6, pady=(6, 6))
        ttk.Label(length_row, text="Длина хода:", width=30,
                  anchor="w").pack(side="left")
        self.turn_length_var = tk.StringVar(
            value=getattr(settings, "turn_length", DEFAULT_TURN_LENGTH)
        )
        length_labels = {
            "short": "Короткий (2-4 предл.)",
            "medium": "Средний (4-8 предл.)",
            "long": "Длинный (8-14 предл.)",
        }
        self._turn_length_reverse = {v: k for k, v in length_labels.items()}
        length_combo = ttk.Combobox(
            length_row,
            values=list(length_labels.values()),
            state="readonly", width=24,
        )
        length_combo.set(
            length_labels.get(self.turn_length_var.get(),
                              length_labels[DEFAULT_TURN_LENGTH])
        )
        length_combo.pack(side="left", padx=(4, 0))
        length_combo.bind(
            "<<ComboboxSelected>>",
            lambda e: self.turn_length_var.set(
                self._turn_length_reverse.get(
                    length_combo.get(), DEFAULT_TURN_LENGTH
                )
            ),
        )

        rpg_frame = ttk.LabelFrame(self.inner, text="RPG-режим")
        rpg_frame.pack(fill="x", **pad)

        self.rpg_var = tk.BooleanVar(value=bool(getattr(cfg, "rpg_mode", False)))
        ttk.Checkbutton(
            rpg_frame,
            text="Включить характеристики и броски d20 против сложности",
            variable=self.rpg_var,
        ).pack(anchor="w", padx=6, pady=(6, 2))

        ttk.Label(
            rpg_frame,
            text="Базовые характеристики через запятую, формат "
                 "«сила:10, ловкость:12, интеллект:8». "
                 "Пусто — значения по умолчанию.",
            foreground="#555", wraplength=600, justify="left",
        ).pack(anchor="w", padx=6, pady=(4, 2))

        existing_stats = getattr(cfg, "base_stats", None) or {}
        stats_source = existing_stats if existing_stats else DEFAULT_STATS
        default_stats_text = ", ".join(
            f"{k}:{v}" for k, v in stats_source.items()
        )
        self.stats_var = tk.StringVar(value=default_stats_text)
        ttk.Entry(rpg_frame, textvariable=self.stats_var).pack(
            fill="x", padx=6, pady=(0, 6)
        )

        text_provider_frame = ttk.LabelFrame(
            self.inner, text="Провайдер текста (ИИ-гейммастер)"
        )
        text_provider_frame.pack(fill="x", **pad)

        self._text_provider_ids = list(TEXT_PROVIDERS.keys())
        text_labels = [TEXT_PROVIDERS[k]["label"] for k in self._text_provider_ids]
        self.text_provider_box = ttk.Combobox(
            text_provider_frame, values=text_labels, state="readonly"
        )
        try:
            text_idx = self._text_provider_ids.index(settings.text_provider)
        except ValueError:
            text_idx = 0
        self.text_provider_box.current(text_idx)
        self.text_provider_box.pack(fill="x", padx=6, pady=(6, 2))
        self.text_provider_box.bind(
            "<<ComboboxSelected>>", lambda e: self._rebuild_text_cred_fields()
        )

        self.text_cred_frame = ttk.Frame(text_provider_frame)
        self.text_cred_frame.pack(fill="x", padx=6, pady=(0, 6))
        self._rebuild_text_cred_fields()

        btns = ttk.Frame(self.inner)
        btns.pack(fill="x", pady=12, padx=10)
        ttk.Button(btns, text="Начать историю", command=self._finish).pack(
            side="right", padx=6
        )
        ttk.Button(btns, text="Отмена", command=self.destroy).pack(side="right")

    def _default_text_pool(self, provider_id: str) -> str:
        existing = self.settings.text_key_pool or []
        if existing and self.settings.text_provider == provider_id:
            return "\n".join(existing)

        info = TEXT_PROVIDERS.get(provider_id, {})
        kind = info.get("kind", "openai")

        if kind == "gigachat":
            auth = os.environ.get("GIGACHAT_AUTH_KEY", "").strip()
            if auth:
                return auth
            cid = os.environ.get("GIGACHAT_CLIENT_ID", "").strip()
            sec = os.environ.get("GIGACHAT_CLIENT_SECRET", "").strip()
            if cid and sec:
                return f"{cid}:{sec}"
        elif kind == "yandex":
            key = os.environ.get("YANDEX_API_KEY", "").strip()
            folder = os.environ.get("YANDEX_FOLDER_ID", "").strip()
            if key and folder:
                return f"{key}:{folder}"
        elif kind == "openai":
            env_names = {
                "openrouter": ["OPENROUTER_API_KEY"],
                "deepseek":   ["DEEPSEEK_API_KEY"],
                "custom":     ["OPENAI_API_KEY"],
            }.get(provider_id, ["OPENAI_API_KEY"])
            for name in env_names:
                v = os.environ.get(name, "").strip()
                if v:
                    return v
        return ""

    def _initial_base_url(self, provider_id: str) -> str:
        saved = (self.settings.text_endpoints or {}).get(provider_id, {})
        if saved.get("base_url"):
            return saved["base_url"]
        return TEXT_PROVIDERS.get(provider_id, {}).get("base_url", "")

    def _initial_model(self, provider_id: str) -> str:
        saved = (self.settings.text_endpoints or {}).get(provider_id, {})
        if saved.get("model"):
            return saved["model"]
        return TEXT_PROVIDERS.get(provider_id, {}).get("model", "")

    def _save_current_cred_values(self):
        """Собирает значения с активных виджетов в _text_* словари."""
        provider = self._last_text_provider
        if not provider:
            return

        pool_widget = getattr(self, "text_pool_widget", None)
        if pool_widget is not None:
            try:
                self._text_pools[provider] = (
                    pool_widget.get("1.0", "end").strip()
                )
            except tk.TclError:
                pass

        base_var = getattr(self, "text_base_url_var", None)
        if base_var is not None:
            try:
                self._text_base_urls[provider] = base_var.get().strip()
            except tk.TclError:
                pass

        model_var = getattr(self, "text_model_var", None)
        if model_var is not None:
            try:
                self._text_models[provider] = model_var.get().strip()
            except tk.TclError:
                pass

    def _rebuild_text_cred_fields(self):
        # 1. Сохранить значения предыдущего провайдера
        self._save_current_cred_values()

        # 2. Очистить контейнер
        for w in self.text_cred_frame.winfo_children():
            w.destroy()

        # 3. Сбросить ссылки на виджеты
        self.text_pool_widget = None
        self.text_base_url_var = None
        self.text_model_var = None

        provider_id = self._text_provider_ids[self.text_provider_box.current()]
        info = TEXT_PROVIDERS[provider_id]
        kind = info.get("kind", "openai")
        self._last_text_provider = provider_id

        # 4. Подсказка
        hint = self._build_cred_hint(provider_id, info, kind)
        if hint:
            ttk.Label(
                self.text_cred_frame, text=hint, foreground="#555",
                wraplength=600, justify="left",
            ).pack(anchor="w", pady=(0, 4))

        # 5. Base URL + Model для OpenAI-совместимых
        if kind == "openai":
            row1 = ttk.Frame(self.text_cred_frame)
            row1.pack(fill="x", pady=(0, 2))
            ttk.Label(row1, text="Base URL:", width=10).pack(side="left")
            self.text_base_url_var = tk.StringVar(
                value=self._initial_base_url(provider_id)
            )
            ttk.Entry(row1, textvariable=self.text_base_url_var).pack(
                side="left", fill="x", expand=True, padx=(4, 0)
            )

            row2 = ttk.Frame(self.text_cred_frame)
            row2.pack(fill="x", pady=(0, 6))
            ttk.Label(row2, text="Модель:", width=10).pack(side="left")
            self.text_model_var = tk.StringVar(
                value=self._initial_model(provider_id)
            )
            ttk.Entry(row2, textvariable=self.text_model_var).pack(
                side="left", fill="x", expand=True, padx=(4, 0)
            )

        # 6. Пул ключей — кроме провайдеров с no_key
        if not info.get("no_key"):
            self.text_pool_widget = tk.Text(
                self.text_cred_frame, height=6, wrap="none",
                font=("Courier", 9),
            )
            self.text_pool_widget.pack(fill="x", pady=(0, 6))

            existing = self._text_pools.get(provider_id, "")
            if not existing:
                existing = self._default_text_pool(provider_id)
            if existing:
                self.text_pool_widget.insert("1.0", existing)
        else:
            # no_key — даём пояснение, что ключ не нужен
            pass

    @staticmethod
    def _build_cred_hint(provider_id: str, info: dict, kind: str) -> str:
        if kind == "gigachat":
            return (
                "Пул ключей GigaChat — по одному на строку:\n"
                "  • Authorization Key из Sber Studio, ИЛИ\n"
                "  • пара client_id:client_secret\n"
                "Бесплатный тариф Freemium. Получить: "
                f"{info.get('signup_url', '')}\n"
                "При исчерпании лимита на текущем ключе программа "
                "автоматически перейдёт к следующему из пула."
            )
        if kind == "yandex":
            return (
                "Пул ключей YandexGPT — по одному на строку в формате:\n"
                "  API_KEY:FOLDER_ID\n"
                f"Получить: {info.get('signup_url', '')}"
            )

        # kind == "openai"
        if provider_id == "openrouter":
            return (
                "Пул ключей OpenRouter — по одному на строку "
                "(формат sk-or-v1-...).\n"
                f"Получить: {info.get('signup_url', '')}\n"
                "Модель — идентификатор OpenRouter, например "
                "openai/gpt-4o-mini, anthropic/claude-3.5-sonnet, "
                "meta-llama/llama-3.1-70b-instruct.\n"
                "При исчерпании лимита на текущем ключе программа "
                "автоматически перейдёт к следующему из пула."
            )
        if provider_id == "deepseek":
            return (
                "Пул ключей DeepSeek — по одному на строку.\n"
                f"Получить: {info.get('signup_url', '')}\n"
                "Модели: deepseek-chat, deepseek-reasoner."
            )
        if provider_id == "ollama":
            return (
                "Локальный сервер Ollama — API-ключ не нужен.\n"
                "Base URL по умолчанию: http://localhost:11434/v1.\n"
                f"Установить Ollama: {info.get('signup_url', '')}\n"
                "Модель должна быть загружена заранее командой вида "
                "`ollama pull llama3.1`."
            )
        if provider_id == "custom":
            return (
                "Любой OpenAI-совместимый сервер: LM Studio, vLLM, "
                "text-generation-webui и т.п.\n"
                "Укажите Base URL (например, http://localhost:8000/v1), "
                "модель и, если требуется, API-ключ."
            )
        return ""

    def _reload_presets(self):
        presets = load_presets()
        self.preset_box["values"] = list(presets.keys())

    def _load_preset(self):
        presets = load_presets()
        name = self.preset_var.get()
        if name in presets:
            cfg = from_dict(presets[name])
            for key, widget in self.vars.items():
                value = getattr(cfg, key)
                if isinstance(widget, tk.StringVar):
                    widget.set(value)
                else:
                    widget.delete("1.0", "end")
                    widget.insert("1.0", value)
            self.rpg_var.set(bool(cfg.rpg_mode))
            stats_src = cfg.base_stats or DEFAULT_STATS
            self.stats_var.set(
                ", ".join(f"{k}:{v}" for k, v in stats_src.items())
            )
            self.moderation_var.set(getattr(cfg, "moderation", "none") or "none")

    def _save_preset_as(self):
        name = simpledialog.askstring(
            "Сохранить пресет", "Название пресета:", parent=self
        )
        if not name:
            return
        cfg = self._collect_cfg()
        save_preset(name, cfg)
        self._reload_presets()
        messagebox.showinfo("Готово", f"Пресет '{name}' сохранён.")

    def _collect_cfg(self) -> StoryConfig:
        values = {}
        for key, widget in self.vars.items():
            if isinstance(widget, tk.StringVar):
                values[key] = widget.get().strip()
            else:
                values[key] = widget.get("1.0", "end").strip()
        values["rpg_mode"] = bool(self.rpg_var.get())
        parsed_stats = _parse_stats_text(self.stats_var.get())
        values["base_stats"] = parsed_stats
        values["moderation"] = self.moderation_var.get() or "none"
        return StoryConfig(**values)

    @staticmethod
    def _parse_pool(text: str) -> list:
        return [line.strip() for line in text.splitlines() if line.strip()]

    def _finish(self):
        cfg = self._collect_cfg()

        text_provider_id = self._text_provider_ids[self.text_provider_box.current()]
        info = TEXT_PROVIDERS[text_provider_id]
        kind = info.get("kind", "openai")
        self.settings.text_provider = text_provider_id

        # --- Параметры генерации ---
        try:
            self.settings.temperature = max(
                0.1, min(1.5, float(self.temperature_var.get()))
            )
        except (tk.TclError, ValueError):
            pass
        try:
            self.settings.max_tokens = max(
                100, min(8000, int(self.max_tokens_var.get()))
            )
        except (tk.TclError, ValueError):
            pass
        try:
            self.settings.top_p = max(
                0.1, min(1.0, float(self.top_p_var.get()))
            )
        except (tk.TclError, ValueError):
            pass
        tl = (self.turn_length_var.get() or "").strip()
        self.settings.turn_length = (
            tl if tl in TURN_LENGTHS else DEFAULT_TURN_LENGTH
        )

        # Считываем значения с активных виджетов
        self._save_current_cred_values()

        # Ключи: для no_key-провайдеров всегда пусто
        if info.get("no_key"):
            self.settings.text_key_pool = []
        else:
            self.settings.text_key_pool = self._parse_pool(
                self._text_pools.get(text_provider_id, "")
            )

        # Endpoints: сохраняем base_url/model только для openai-kind
        endpoints = dict(self.settings.text_endpoints or {})
        if kind == "openai":
            base_url = self._text_base_urls.get(text_provider_id, "").strip()
            model = self._text_models.get(text_provider_id, "").strip()
            endpoints[text_provider_id] = {
                "base_url": base_url,
                "model": model,
            }
        self.settings.text_endpoints = endpoints

        # Пробрасываем в env — только для классических провайдеров
        if kind == "gigachat" and self.settings.text_key_pool:
            os.environ["GIGACHAT_AUTH_KEY"] = self.settings.text_key_pool[0]
        elif kind == "yandex" and self.settings.text_key_pool:
            entry = self.settings.text_key_pool[0]
            api_key, _, folder = entry.rpartition(":")
            if api_key and folder:
                os.environ["YANDEX_API_KEY"] = api_key.strip()
                os.environ["YANDEX_FOLDER_ID"] = folder.strip()

        try:
            save_settings(self.settings)
        except Exception as e:
            # Не роняем окно настройки, если, например, keyring
            # недоступен — просто покажем предупреждение.
            messagebox.showwarning(
                "Настройки",
                f"Не удалось сохранить настройки:\n{e}\n"
                "Ключи могут не сохраниться между запусками.",
            )
        self.destroy()
        self.on_done(cfg, self.settings)


# ---------------------------------------------------------------------------
# Окно инвентаря
# ---------------------------------------------------------------------------

class InventoryWindow(tk.Toplevel):
    def __init__(self, master, player_state: PlayerState, on_change=None):
        super().__init__(master)
        self.title(f"Инвентарь и экипировка — {player_state.name}")
        self.geometry("820x600")
        self.minsize(720, 480)
        self.player_state = player_state
        self.on_change = on_change

        top = ttk.Frame(self)
        top.pack(fill="x", padx=8, pady=6)
        ttk.Label(top, text=f"Игрок: {player_state.name}",
                  font=("TkDefaultFont", 11, "bold")).pack(side="left")
        ttk.Button(top, text="+ Добавить предмет",
                   command=self._add_manual).pack(side="right", padx=4)
        ttk.Button(top, text="Обновить",
                   command=self.refresh).pack(side="right")

        body = ttk.Frame(self)
        body.pack(fill="both", expand=True, padx=8, pady=(0, 8))

        left = ttk.LabelFrame(body, text="Рюкзак")
        left.pack(side="left", fill="both", expand=True)
        self.inv_list = tk.Listbox(left, font=("Consolas", 10), activestyle="dotbox")
        inv_scroll = ttk.Scrollbar(left, orient="vertical", command=self.inv_list.yview)
        self.inv_list.configure(yscrollcommand=inv_scroll.set)
        self.inv_list.pack(side="left", fill="both", expand=True, padx=(6, 0), pady=6)
        inv_scroll.pack(side="right", fill="y", pady=6)
        self.inv_list.bind("<Double-Button-1>", lambda e: self._equip_selected())

        mid = ttk.Frame(body)
        mid.pack(side="left", fill="y", padx=8)
        ttk.Button(mid, text="Снарядить →",
                   command=self._equip_selected).pack(pady=4, fill="x")
        ttk.Button(mid, text="Снять всё ←",
                   command=self._unequip_all).pack(pady=4, fill="x")
        ttk.Button(mid, text="Редактировать...",
                   command=self._edit_selected).pack(pady=4, fill="x")
        ttk.Button(mid, text="Удалить",
                   command=self._delete_selected).pack(pady=4, fill="x")
        ttk.Label(mid, text="Двойной клик\nпо предмету —\nснарядить",
                  foreground="#666", justify="center").pack(pady=(14, 0))

        right = ttk.LabelFrame(body, text="Тело / Экипировка")
        right.pack(side="left", fill="both", expand=True)

        self.slot_buttons = {}
        for sid, slabel in EQUIPMENT_SLOTS:
            row = ttk.Frame(right)
            row.pack(fill="x", padx=6, pady=2)
            ttk.Label(row, text=slabel + ":", width=20,
                      anchor="w").pack(side="left")
            btn = ttk.Button(row, text="— пусто —", width=32,
                             command=lambda s=sid: self._click_slot(s))
            btn.pack(side="left", fill="x", expand=True)
            self.slot_buttons[sid] = btn

        self.refresh()

    def _selected_index(self):
        sel = self.inv_list.curselection()
        if not sel:
            return None
        return int(sel[0])

    def _notify(self):
        if self.on_change:
            try:
                self.on_change()
            except Exception:
                pass

    def refresh(self):
        self.inv_list.delete(0, "end")
        for it in self.player_state.inventory:
            nm = it.get("name", "?")
            desc = (it.get("description") or "").strip().replace("\n", " ")
            short = (desc[:55] + "…") if len(desc) > 55 else desc
            slot = it.get("equip_slot") or PlayerState.guess_slot(it) or ""
            tag = f" [{slot}]" if slot else ""
            self.inv_list.insert("end", f"{nm}{tag}" + (f" — {short}" if short else ""))

        for sid, _label in EQUIPMENT_SLOTS:
            item = self.player_state.equipped.get(sid)
            btn = self.slot_buttons[sid]
            if item:
                btn.configure(text=item.get("name", "?"))
            else:
                btn.configure(text="— пусто —")

    def _equip_selected(self):
        idx = self._selected_index()
        if idx is None:
            messagebox.showinfo("Инвентарь", "Выберите предмет в рюкзаке.",
                                parent=self)
            return
        slot, err = self.player_state.equip(idx)
        if err:
            if not messagebox.askyesno(
                "Слот не определён",
                err + "\n\nОткрыть редактор предмета и указать слот вручную?",
                parent=self,
            ):
                return
            item = self.player_state.inventory[idx]
            ItemEditor(self, item, on_save=lambda _it: (self.refresh(), self._notify()))
            return
        self.refresh()
        self._notify()

    def _click_slot(self, slot_id):
        item = self.player_state.equipped.get(slot_id)
        if item is not None:
            self.player_state.unequip(slot_id)
            self.refresh()
            self._notify()
            return
        idx = self._selected_index()
        if idx is None:
            return
        err = self.player_state.equip_into_slot(idx, slot_id)
        if err:
            messagebox.showerror("Инвентарь", err, parent=self)
            return
        self.refresh()
        self._notify()

    def _unequip_all(self):
        if not self.player_state.equipped:
            return
        for slot_id in list(self.player_state.equipped.keys()):
            self.player_state.unequip(slot_id)
        self.refresh()
        self._notify()

    def _edit_selected(self):
        idx = self._selected_index()
        if idx is None:
            messagebox.showinfo("Инвентарь", "Выберите предмет.",
                                parent=self)
            return
        item = self.player_state.inventory[idx]
        ItemEditor(self, item, on_save=lambda _it: (self.refresh(), self._notify()))

    def _delete_selected(self):
        idx = self._selected_index()
        if idx is None:
            return
        item = self.player_state.inventory[idx]
        if messagebox.askyesno(
            "Удалить", f"Удалить «{item.get('name','?')}» из рюкзака?",
            parent=self,
        ):
            del self.player_state.inventory[idx]
            self.refresh()
            self._notify()

    def _add_manual(self):
        def _save(new_item):
            self.player_state.add_item(new_item)
            self.refresh()
            self._notify()

        ItemEditor(self, {"name": "Новый предмет", "type": "предмет",
                          "description": "", "properties": {}}, on_save=_save)

class StatsWindow(tk.Toplevel):
    """
    Редактор характеристик героя.
    Показывает базовые значения, бонус от экипировки и итог.
    """

    def __init__(self, master, player_state: PlayerState, on_change=None):
        super().__init__(master)
        self.title(f"Характеристики — {player_state.name}")
        self.geometry("440x420")
        self.minsize(400, 360)
        self.transient(master)
        self.grab_set()
        self.player_state = player_state
        self.on_change = on_change

        top = ttk.Frame(self)
        top.pack(fill="x", padx=10, pady=(10, 4))
        ttk.Label(
            top,
            text="Базовые характеристики и бонусы от экипировки.",
            foreground="#555",
        ).pack(anchor="w")

        grid = ttk.Frame(self)
        grid.pack(fill="both", expand=True, padx=10, pady=6)

        headers = ["Характеристика", "База", "Бонус", "Итого"]
        for col, h in enumerate(headers):
            ttk.Label(grid, text=h, font=("TkDefaultFont", 10, "bold")).grid(
                row=0, column=col, padx=6, pady=(4, 8), sticky="w"
            )

        self.entries = {}
        row = 1
        stats_order = list(DEFAULT_STATS.keys())
        for k in self.player_state.stats.keys():
            if k not in stats_order:
                stats_order.append(k)

        for stat in stats_order:
            ttk.Label(grid, text=stat, width=14, anchor="w").grid(
                row=row, column=0, padx=6, pady=3, sticky="w"
            )
            var = tk.StringVar(value=str(self.player_state.stats.get(stat, 0)))
            ent = ttk.Entry(grid, textvariable=var, width=8)
            ent.grid(row=row, column=1, padx=6, pady=3, sticky="w")
            ent.bind("<FocusOut>", lambda e: self._recompute())
            ent.bind("<Return>", lambda e: self._recompute())
            self.entries[stat] = var

            bonus_lbl = ttk.Label(grid, text="", width=8, anchor="w")
            bonus_lbl.grid(row=row, column=2, padx=6, pady=3, sticky="w")
            total_lbl = ttk.Label(grid, text="", width=8, anchor="w")
            total_lbl.grid(row=row, column=3, padx=6, pady=3, sticky="w")
            self._bonus_labels = getattr(self, "_bonus_labels", {})
            self._total_labels = getattr(self, "_total_labels", {})
            self._bonus_labels[stat] = bonus_lbl
            self._total_labels[stat] = total_lbl
            row += 1

        btns = ttk.Frame(self)
        btns.pack(fill="x", padx=10, pady=(4, 10))
        ttk.Button(btns, text="Сохранить", command=self._save).pack(side="right")
        ttk.Button(btns, text="Сброс к базовым", command=self._reset_defaults).pack(
            side="right", padx=6
        )
        ttk.Button(btns, text="Отмена", command=self.destroy).pack(side="right")

        self._recompute()

    def _apply_entries_to_state(self):
        """Промежуточно записывает значения из полей в player_state.stats,
        чтобы get_effective_stats() показал свежие бонусы."""
        for stat, var in self.entries.items():
            try:
                self.player_state.stats[stat] = int(var.get())
            except ValueError:
                pass

    def _recompute(self):
        self._apply_entries_to_state()
        eff = self.player_state.get_effective_stats()
        for stat, var in self.entries.items():
            base = self.player_state.stats.get(stat, 0)
            total = eff.get(stat, base)
            bonus = total - base
            self._bonus_labels[stat].configure(
                text=(f"+{bonus}" if bonus > 0 else (str(bonus) if bonus < 0 else "—"))
            )
            self._total_labels[stat].configure(text=str(total))

    def _reset_defaults(self):
        for stat in self.entries:
            default = DEFAULT_STATS.get(stat, 10)
            self.entries[stat].set(str(default))
        self._recompute()

    def _save(self):
        self._apply_entries_to_state()
        self.destroy()
        if self.on_change:
            try:
                self.on_change()
            except Exception:
                pass


class ScrollableTab(ttk.Frame):
    """Вкладка Notebook с прокруткой (используется в CardsWindow/QuestWindow).

    _canvas/_inner заполняются в _build_scroll(), но объявлены здесь явно —
    у обычного ttk.Frame таких атрибутов нет, и без этого подкласса их
    навешивание "на лету" не только сбивает статический анализ, но и может
    незаметно обернуться AttributeError, если что-то обратится к вкладке до
    вызова _build_scroll().
    """

    def __init__(self, master=None, **kwargs):
        super().__init__(master, **kwargs)
        self._canvas = None
        self._inner = None


# ---------------------------------------------------------------------------
# Окно карточек
# ---------------------------------------------------------------------------

class CardsWindow(tk.Toplevel):
    """
    Окно карточек с четырьмя вкладками:
      * «Предметы»   — все предметы, можно положить в рюкзак;
      * «Бестиарий»  — существа и NPC со статусом/HP/отношением;
      * «Локации»    — те же карточки, сгруппированные по полю location;
      * «Все»        — единый список.
    """

    def __init__(self, master, store: CardStore,
                 player_state: PlayerState = None,
                 on_inventory_change=None):
        super().__init__(master)
        self.title("Карточки и бестиарий")
        self.geometry("760x660")
        self.minsize(620, 520)
        self.store = store
        self.player_state = player_state
        self.on_inventory_change = on_inventory_change

        top = ttk.Frame(self)
        top.pack(fill="x", pady=6, padx=6)
        ttk.Button(top, text="Экспорт в Markdown (с оглавлением)",
                   command=self._export_md).pack(side="left", padx=4)
        ttk.Button(top, text="Экспорт в JSON",
                   command=self._export_json).pack(side="left", padx=4)
        ttk.Button(top, text="Обновить", command=self.refresh).pack(
            side="right", padx=4
        )

        self.notebook = ttk.Notebook(self)
        self.notebook.pack(fill="both", expand=True, padx=6, pady=(0, 6))

        self.tab_items = ScrollableTab(self.notebook)
        self.tab_bestiary = ScrollableTab(self.notebook)
        self.tab_locations = ScrollableTab(self.notebook)
        self.tab_all = ScrollableTab(self.notebook)

        self.notebook.add(self.tab_items, text="Предметы")
        self.notebook.add(self.tab_bestiary, text="Бестиарий")
        self.notebook.add(self.tab_locations, text="Локации")
        self.notebook.add(self.tab_all, text="Все")

        for tab in (self.tab_items, self.tab_bestiary,
                    self.tab_locations, self.tab_all):
            self._build_scroll(tab)

        # Прокрутка колесом — только пока курсор внутри окна, и с учётом
        # активной вкладки (иначе колесо дёргало бы скрытые canvas-ы).
        self.bind("<Enter>", self._bind_wheel)
        self.bind("<Leave>", self._unbind_wheel)

        self.refresh()

    # -- Служебное ---------------------------------------------------------

    def _build_scroll(self, tab):
        canvas = tk.Canvas(tab, highlightthickness=0)
        scroll = ttk.Scrollbar(tab, orient="vertical", command=canvas.yview)
        inner = ttk.Frame(canvas)
        inner.bind(
            "<Configure>",
            lambda e, c=canvas: c.configure(scrollregion=c.bbox("all")),
        )
        canvas.create_window((0, 0), window=inner, anchor="nw")
        canvas.configure(yscrollcommand=scroll.set)
        canvas.pack(side="left", fill="both", expand=True)
        scroll.pack(side="right", fill="y")

        def _on_wheel(event, c=canvas):
            try:
                if c.winfo_exists():
                    c.yview_scroll(int(-1 * (event.delta / 120)), "units")
            except tk.TclError:
                pass

        canvas._wheel_handler = _on_wheel  # ссылка на случай уничтожения
        tab._canvas = canvas
        tab._inner = inner

    def _bind_wheel(self, _e=None):
        try:
            current = self.notebook.nametowidget(self.notebook.select())
        except tk.TclError:
            return
        canvas = getattr(current, "_canvas", None)
        handler = getattr(canvas, "_wheel_handler", None)
        if handler:
            try:
                self.bind_all("<MouseWheel>", handler)
            except tk.TclError:
                pass

    def _unbind_wheel(self, _e=None):
        try:
            self.unbind_all("<MouseWheel>")
        except tk.TclError:
            pass

    def _clear_inner(self, tab):
        # tab._inner может быть ещё None, если _build_scroll() для этой
        # вкладки почему-то не был вызван — не падаем молча AttributeError'ом.
        if tab._inner is None:
            return
        for w in tab._inner.winfo_children():
            w.destroy()

    # -- Перерисовка -------------------------------------------------------

    def refresh(self):
        self._render_tab(self.tab_items,
                         self.store.by_type("предмет"),
                         show_to_inventory=True)
        self._render_tab(self.tab_bestiary,
                         self.store.by_type("существо"),
                         show_to_inventory=False)
        self._render_locations_tab()
        self._render_tab(self.tab_all, self.store.cards,
                         show_to_inventory=True)

    def _render_tab(self, tab, cards, show_to_inventory=False):
        self._clear_inner(tab)
        if not cards:
            ttk.Label(
                tab._inner,
                text="Пока нет карточек этого типа.",
                foreground="#666",
            ).pack(padx=10, pady=10)
            return
        for card in cards:
            self._render_card(tab._inner, card, show_to_inventory)

    def _render_locations_tab(self):
        self._clear_inner(self.tab_locations)
        by_loc = {}
        no_loc = []
        for c in self.store.cards:
            loc = c.get("location")
            if loc:
                by_loc.setdefault(str(loc), []).append(c)
            else:
                no_loc.append(c)

        if not by_loc and not no_loc:
            ttk.Label(
                self.tab_locations._inner,
                text="Пока нет карточек.",
                foreground="#666",
            ).pack(padx=10, pady=10)
            return

        for loc in sorted(by_loc.keys()):
            ttk.Label(
                self.tab_locations._inner,
                text=f"📍 {loc}  ({len(by_loc[loc])})",
                font=("TkDefaultFont", 11, "bold"),
            ).pack(anchor="w", padx=10, pady=(10, 2))
            for card in by_loc[loc]:
                self._render_card(self.tab_locations._inner, card,
                                  show_to_inventory=True)

        if no_loc:
            ttk.Label(
                self.tab_locations._inner,
                text=f"Без локации  ({len(no_loc)})",
                font=("TkDefaultFont", 11, "bold"),
            ).pack(anchor="w", padx=10, pady=(10, 2))
            for card in no_loc:
                self._render_card(self.tab_locations._inner, card,
                                  show_to_inventory=True)

    def _render_card(self, parent, card, show_to_inventory):
        name = card.get("name", "?")
        type_ = card.get("type", "предмет")

        badges = []
        if card.get("status"):
            badges.append(str(card["status"]))
        if card.get("attitude"):
            badges.append(str(card["attitude"]))
        if card.get("hp") not in (None, ""):
            badges.append(f"HP {card['hp']}")
        if card.get("location"):
            badges.append(f"@ {card['location']}")
        badge_str = f"  [{', '.join(badges)}]" if badges else ""

        frame = ttk.LabelFrame(parent, text=f"{name}  ({type_}){badge_str}")
        frame.pack(fill="x", padx=8, pady=6)

        text_col = ttk.Frame(frame)
        text_col.pack(fill="x", padx=6, pady=4)
        if card.get("description"):
            ttk.Label(
                text_col, text=card["description"],
                wraplength=620, justify="left",
            ).pack(anchor="w")
        props = card.get("properties") or {}
        if props:
            props_str = "; ".join(f"{k}: {v}" for k, v in props.items())
            ttk.Label(
                text_col, text=props_str, wraplength=620, foreground="#555",
            ).pack(anchor="w", pady=(4, 0))

        btn_row = ttk.Frame(frame)
        btn_row.pack(fill="x", pady=4)

        if (show_to_inventory and self.player_state is not None
                and str(type_).lower() != "существо"):
            ttk.Button(
                btn_row, text="В рюкзак",
                command=lambda c=card: self._to_inventory(c),
            ).pack(side="left", padx=6)

        ttk.Button(
            btn_row, text="Изменить статус...",
            command=lambda c=card: self._edit_status(c),
        ).pack(side="left", padx=6)

        ttk.Button(
            btn_row, text="Удалить",
            command=lambda c=card: self._delete_card(c),
        ).pack(side="left", padx=6)

    # -- Действия ----------------------------------------------------------

    def _to_inventory(self, card):
        item = {
            "name": card.get("name", "Без названия"),
            "type": card.get("type", "предмет"),
            "description": card.get("description", ""),
            "properties": dict(card.get("properties") or {}),
        }
        if card.get("equip_slot"):
            item["equip_slot"] = card["equip_slot"]
        self.player_state.add_item(item)
        messagebox.showinfo(
            "Инвентарь",
            f"«{item['name']}» добавлено в рюкзак.",
            parent=self,
        )
        if self.on_inventory_change:
            try:
                self.on_inventory_change()
            except Exception:
                pass

    def _edit_status(self, card):
        dlg = tk.Toplevel(self)
        dlg.title(f"Изменить — {card.get('name', '?')}")
        dlg.geometry("440x400")
        dlg.transient(self)
        dlg.grab_set()

        frm = ttk.Frame(dlg)
        frm.pack(fill="both", expand=True, padx=12, pady=12)

        ttk.Label(frm, text="Статус:").pack(anchor="w")
        status_var = tk.StringVar(value=card.get("status") or "")
        ttk.Combobox(
            frm, textvariable=status_var,
            values=[""] + CARD_STATUSES, state="readonly",
        ).pack(fill="x", pady=(0, 8))

        ttk.Label(frm, text="Отношение (для существ):").pack(anchor="w")
        attitude_var = tk.StringVar(value=card.get("attitude") or "")
        ttk.Combobox(
            frm, textvariable=attitude_var,
            values=[""] + CARD_ATTITUDES, state="readonly",
        ).pack(fill="x", pady=(0, 8))

        ttk.Label(frm, text="HP (здоровье):").pack(anchor="w")
        hp_var = tk.StringVar(value=str(card.get("hp") or ""))
        ttk.Entry(frm, textvariable=hp_var).pack(fill="x", pady=(0, 8))

        ttk.Label(frm, text="Локация:").pack(anchor="w")
        loc_var = tk.StringVar(value=card.get("location") or "")
        # Комбобокс с уже существующими локациями + возможность ввести новую.
        ttk.Combobox(
            frm, textvariable=loc_var,
            values=[""] + self.store.locations(),
        ).pack(fill="x", pady=(0, 8))

        btns = ttk.Frame(frm)
        btns.pack(fill="x", pady=(10, 0))

        def _save():
            card["status"] = status_var.get().strip() or None
            card["attitude"] = attitude_var.get().strip() or None
            hp_val = hp_var.get().strip()
            card["hp"] = hp_val if hp_val else None
            card["location"] = loc_var.get().strip() or None
            dlg.destroy()
            self.refresh()

        ttk.Button(btns, text="Сохранить", command=_save).pack(side="right")
        ttk.Button(btns, text="Отмена", command=dlg.destroy).pack(
            side="right", padx=6
        )

    def _delete_card(self, card):
        if not messagebox.askyesno(
            "Удалить",
            f"Удалить карточку «{card.get('name', '?')}»?",
            parent=self,
        ):
            return
        self.store.remove(card)
        self.refresh()

    # -- Экспорт -----------------------------------------------------------

    def _export_md(self):
        path = filedialog.asksaveasfilename(
            defaultextension=".md",
            filetypes=[("Markdown", "*.md"), ("Все файлы", "*.*")],
        )
        if path:
            self.store.export_markdown(path)
            messagebox.showinfo("Готово",
                                f"Карточки экспортированы в {path}")

    def _export_json(self):
        path = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=[("JSON", "*.json"), ("Все файлы", "*.*")],
        )
        if path:
            self.store.export_json(path)
            messagebox.showinfo("Готово",
                                f"Карточки экспортированы в {path}")

# ---------------------------------------------------------------------------
# Окно журнала квестов
# ---------------------------------------------------------------------------

class QuestWindow(tk.Toplevel):
    """
    Журнал квестов с вкладками:
      * Активные    — что герой сейчас делает;
      * Выполненные — успешно завершённые;
      * Проваленные — провалы;
      * Все         — единый список.
    """

    def __init__(self, master, store: QuestStore, on_change=None):
        super().__init__(master)
        self.title("Журнал квестов")
        self.geometry("680x600")
        self.minsize(560, 440)
        self.store = store
        self.on_change = on_change

        top = ttk.Frame(self)
        top.pack(fill="x", padx=8, pady=6)
        ttk.Button(top, text="Экспорт в Markdown",
                   command=self._export_md).pack(side="left", padx=4)
        ttk.Button(top, text="Экспорт в JSON",
                   command=self._export_json).pack(side="left", padx=4)
        ttk.Button(top, text="Обновить",
                   command=self.refresh).pack(side="right", padx=4)

        self.notebook = ttk.Notebook(self)
        self.notebook.pack(fill="both", expand=True, padx=8, pady=(0, 8))

        self.tab_active = ScrollableTab(self.notebook)
        self.tab_done = ScrollableTab(self.notebook)
        self.tab_failed = ScrollableTab(self.notebook)
        self.tab_all = ScrollableTab(self.notebook)

        self.notebook.add(self.tab_active, text="Активные")
        self.notebook.add(self.tab_done, text="Выполненные")
        self.notebook.add(self.tab_failed, text="Проваленные")
        self.notebook.add(self.tab_all, text="Все")

        for tab in (self.tab_active, self.tab_done,
                    self.tab_failed, self.tab_all):
            self._build_scroll(tab)

        self.bind("<Enter>", self._bind_wheel)
        self.bind("<Leave>", self._unbind_wheel)

        self.refresh()

    # -- Служебное ---------------------------------------------------------

    def _build_scroll(self, tab):
        canvas = tk.Canvas(tab, highlightthickness=0)
        scroll = ttk.Scrollbar(tab, orient="vertical", command=canvas.yview)
        inner = ttk.Frame(canvas)
        inner.bind(
            "<Configure>",
            lambda e, c=canvas: c.configure(scrollregion=c.bbox("all")),
        )
        canvas.create_window((0, 0), window=inner, anchor="nw")
        canvas.configure(yscrollcommand=scroll.set)
        canvas.pack(side="left", fill="both", expand=True)
        scroll.pack(side="right", fill="y")

        def _on_wheel(event, c=canvas):
            try:
                if c.winfo_exists():
                    c.yview_scroll(int(-1 * (event.delta / 120)), "units")
            except tk.TclError:
                pass

        canvas._wheel_handler = _on_wheel
        tab._canvas = canvas
        tab._inner = inner

    def _bind_wheel(self, _e=None):
        try:
            current = self.notebook.nametowidget(self.notebook.select())
        except tk.TclError:
            return
        canvas = getattr(current, "_canvas", None)
        handler = getattr(canvas, "_wheel_handler", None)
        if handler:
            try:
                self.bind_all("<MouseWheel>", handler)
            except tk.TclError:
                pass

    def _unbind_wheel(self, _e=None):
        try:
            self.unbind_all("<MouseWheel>")
        except tk.TclError:
            pass

    def _clear_inner(self, tab):
        # tab._inner может быть ещё None, если _build_scroll() для этой
        # вкладки почему-то не был вызван — не падаем молча AttributeError'ом.
        if tab._inner is None:
            return
        for w in tab._inner.winfo_children():
            w.destroy()

    def _notify(self):
        if self.on_change:
            try:
                self.on_change()
            except Exception:
                pass

    # -- Перерисовка -------------------------------------------------------

    def refresh(self):
        self._render_tab(self.tab_active, self.store.by_status("active"))
        self._render_tab(self.tab_done, self.store.by_status("done"))
        self._render_tab(self.tab_failed, self.store.by_status("failed"))
        self._render_tab(self.tab_all, self.store.quests)

    def _render_tab(self, tab, quests):
        self._clear_inner(tab)
        if not quests:
            ttk.Label(
                tab._inner,
                text="Здесь пока пусто.",
                foreground="#666",
            ).pack(padx=10, pady=10)
            return
        for q in quests:
            self._render_quest(tab._inner, q)

    def _render_quest(self, parent, q):
        status = q.get("status", "active")
        status_label = QUEST_STATUS_LABELS.get(status, status)

        header = f"{q.get('name', '?')}   [{status_label}]"
        frame = ttk.LabelFrame(parent, text=header)
        frame.pack(fill="x", padx=8, pady=6)

        text_col = ttk.Frame(frame)
        text_col.pack(fill="x", padx=6, pady=4)
        if q.get("description"):
            ttk.Label(
                text_col, text=q["description"],
                wraplength=600, justify="left",
            ).pack(anchor="w")

        meta_bits = []
        if q.get("created_at"):
            meta_bits.append(f"открыт на ходу {q['created_at']}")
        if q.get("updated_at") and q["updated_at"] != q.get("created_at"):
            meta_bits.append(f"обновлён на ходу {q['updated_at']}")
        if meta_bits:
            ttk.Label(
                text_col, text="; ".join(meta_bits),
                foreground="#777",
            ).pack(anchor="w", pady=(4, 0))

        btn_row = ttk.Frame(frame)
        btn_row.pack(fill="x", pady=4)

        if status != "active":
            ttk.Button(
                btn_row, text="Вернуть в активные",
                command=lambda quest=q: self._set_status(quest, "active"),
            ).pack(side="left", padx=6)
        if status != "done":
            ttk.Button(
                btn_row, text="Отметить выполненным",
                command=lambda quest=q: self._set_status(quest, "done"),
            ).pack(side="left", padx=6)
        if status != "failed":
            ttk.Button(
                btn_row, text="Отметить проваленным",
                command=lambda quest=q: self._set_status(quest, "failed"),
            ).pack(side="left", padx=6)

        ttk.Button(
            btn_row, text="Удалить",
            command=lambda quest=q: self._delete_quest(quest),
        ).pack(side="right", padx=6)

    # -- Действия ----------------------------------------------------------

    def _set_status(self, quest, status):
        self.store.set_status(quest, status)
        self.refresh()
        self._notify()

    def _delete_quest(self, quest):
        if not messagebox.askyesno(
            "Удалить",
            f"Удалить квест «{quest.get('name', '?')}» из журнала?",
            parent=self,
        ):
            return
        self.store.remove(quest)
        self.refresh()
        self._notify()

    # -- Экспорт -----------------------------------------------------------

    def _export_md(self):
        path = filedialog.asksaveasfilename(
            defaultextension=".md",
            filetypes=[("Markdown", "*.md"), ("Все файлы", "*.*")],
        )
        if path:
            self.store.export_markdown(path)
            messagebox.showinfo("Готово",
                                f"Журнал экспортирован в {path}")

    def _export_json(self):
        path = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=[("JSON", "*.json"), ("Все файлы", "*.*")],
        )
        if path:
            self.store.export_json(path)
            messagebox.showinfo("Готово",
                                f"Журнал экспортирован в {path}")

class FactsWindow(tk.Toplevel):
    """
    Редактор «важных фактов» — многоуровневая память сюжета.
    Правки сразу попадают в system prompt следующего хода.
    """

    def __init__(self, master, facts: list, on_save=None):
        super().__init__(master)
        self.title("Важные факты")
        self.geometry("560x500")
        self.minsize(480, 400)
        self.transient(master)
        self.grab_set()
        self._on_save = on_save
        self._facts = list(facts or [])

        info = ttk.Label(
            self,
            text="Эти факты считаются каноном и попадают в системный промпт "
                 "перед каждым ходом. Записывайте только то, что должно "
                 "оставаться неизменным (имена, названия, договорённости, "
                 "важные события).",
            foreground="#555", wraplength=520, justify="left",
        )
        info.pack(fill="x", padx=12, pady=(10, 6))

        body = ttk.Frame(self)
        body.pack(fill="both", expand=True, padx=12, pady=(0, 6))

        self.listbox = tk.Listbox(body, font=("TkDefaultFont", 10),
                                  activestyle="dotbox")
        scroll = ttk.Scrollbar(body, orient="vertical",
                               command=self.listbox.yview)
        self.listbox.configure(yscrollcommand=scroll.set)
        self.listbox.pack(side="left", fill="both", expand=True)
        scroll.pack(side="right", fill="y")
        self.listbox.bind("<Double-Button-1>", lambda e: self._edit_selected())

        btns = ttk.Frame(self)
        btns.pack(fill="x", padx=12, pady=(0, 6))
        ttk.Button(btns, text="+ Добавить", command=self._add).pack(
            side="left", padx=(0, 4))
        ttk.Button(btns, text="Изменить", command=self._edit_selected).pack(
            side="left", padx=4)
        ttk.Button(btns, text="Удалить", command=self._delete_selected).pack(
            side="left", padx=4)
        ttk.Button(btns, text="Вверх", command=lambda: self._move(-1)).pack(
            side="right", padx=(4, 0))
        ttk.Button(btns, text="Вниз", command=lambda: self._move(1)).pack(
            side="right", padx=(4, 0))

        footer = ttk.Frame(self)
        footer.pack(fill="x", padx=12, pady=(0, 12))
        ttk.Button(footer, text="Сохранить", command=self._save).pack(
            side="right")
        ttk.Button(footer, text="Отмена", command=self.destroy).pack(
            side="right", padx=6)

        self._refresh()

    def _refresh(self):
        self.listbox.delete(0, "end")
        for i, f in enumerate(self._facts, 1):
            short = f if len(f) <= 90 else f[:89] + "…"
            self.listbox.insert("end", f"{i}. {short}")

    def _selected_index(self):
        sel = self.listbox.curselection()
        if not sel:
            return None
        return int(sel[0])

    def _add(self):
        text = simpledialog.askstring("Новый факт",
                                      "Опишите факт:", parent=self)
        if not text:
            return
        text = text.strip()
        if not text:
            return
        self._facts.append(text)
        self._refresh()
        self.listbox.selection_clear(0, "end")
        self.listbox.selection_set("end")
        self.listbox.see("end")

    def _edit_selected(self):
        idx = self._selected_index()
        if idx is None:
            return
        text = simpledialog.askstring(
            "Изменить факт", "Отредактируйте:", parent=self,
            initialvalue=self._facts[idx],
        )
        if text is None:
            return
        text = text.strip()
        if not text:
            return
        self._facts[idx] = text
        self._refresh()
        self.listbox.selection_set(idx)

    def _delete_selected(self):
        idx = self._selected_index()
        if idx is None:
            return
        if not messagebox.askyesno(
            "Удалить", f"Удалить факт №{idx + 1}?", parent=self,
        ):
            return
        del self._facts[idx]
        self._refresh()

    def _move(self, delta):
        idx = self._selected_index()
        if idx is None:
            return
        new_idx = idx + delta
        if not (0 <= new_idx < len(self._facts)):
            return
        self._facts[idx], self._facts[new_idx] = \
            self._facts[new_idx], self._facts[idx]
        self._refresh()
        self.listbox.selection_set(new_idx)

    def _save(self):
        if self._on_save:
            try:
                self._on_save(list(self._facts))
            except Exception:
                pass
        self.destroy()

class SessionStatsWindow(tk.Toplevel):
    """
    Детальная статистика сессии: ходы, символы, токены, оценка стоимости.
    """

    def __init__(self, master, stats: SessionStats, provider_id: str):
        super().__init__(master)
        self.title("Статистика сессии")
        self.geometry("560x520")
        self.minsize(480, 420)
        self.transient(master)
        self.grab_set()
        self.stats = stats
        self.provider_id = provider_id

        info = ttk.Label(
            self,
            text="Счётчики накапливаются с момента запуска сессии "
                 "(и восстанавливаются из сейвов).\n"
                 "Токены учитываются только если провайдер вернул usage "
                 "в ответе.",
            foreground="#555", wraplength=520, justify="left",
        )
        info.pack(fill="x", padx=12, pady=(10, 6))

        body = ttk.Frame(self)
        body.pack(fill="both", expand=True, padx=12, pady=(0, 6))

        cols = ["Показатель", "Значение"]
        for i, h in enumerate(cols):
            ttk.Label(body, text=h,
                      font=("TkDefaultFont", 10, "bold")).grid(
                row=0, column=i, padx=6, pady=(4, 8), sticky="w"
            )

        rows = [
            ("Ходов", str(stats.turns)),
            ("Символов отправлено", str(stats.chars_in)),
            ("Символов получено", str(stats.chars_out)),
            ("Токенов prompt (input)",
             f"{stats.tokens_in}" if stats.tokens_reports else "—"),
            ("Токенов completion (output)",
             f"{stats.tokens_out}" if stats.tokens_reports else "—"),
            ("Ответов с usage", f"{stats.tokens_reports}"),
            ("Ошибок", str(stats.errors)),
        ]

        r = 1
        for label, value in rows:
            ttk.Label(body, text=label, anchor="w").grid(
                row=r, column=0, padx=6, pady=3, sticky="w"
            )
            ttk.Label(body, text=value, anchor="e",
                      font=("Consolas", 10)).grid(
                row=r, column=1, padx=6, pady=3, sticky="e"
            )
            r += 1

        ttk.Separator(body, orient="horizontal").grid(
            row=r, column=0, columnspan=2, sticky="ew", pady=8
        )
        r += 1

        currency, cost = stats.estimate_cost(provider_id)
        if currency and currency != "—" and stats.tokens_reports:
            cost_text = f"~{cost:.4f} {currency}"
        elif currency == "—":
            cost_text = "локальный сервер (без оплаты)"
        elif not stats.tokens_reports:
            cost_text = "недоступно (нет usage от провайдера)"
        else:
            cost_text = "—"

        ttk.Label(
            body, text="Оценка стоимости (по текущему провайдеру)",
            anchor="w", font=("TkDefaultFont", 10, "bold"),
        ).grid(row=r, column=0, columnspan=2, padx=6, pady=(4, 2), sticky="w")
        r += 1
        ttk.Label(body, text=cost_text, anchor="e",
                  font=("Consolas", 10)).grid(
            row=r, column=0, columnspan=2, padx=6, pady=2, sticky="e"
        )
        r += 1

        ttk.Label(
            body,
            text=f"Провайдер: {provider_id}. Стоимость приблизительна — "
                 "уточняйте тарифы у провайдера.",
            foreground="#777", wraplength=500, justify="left",
        ).grid(row=r, column=0, columnspan=2, padx=6, pady=(6, 2), sticky="w")

        footer = ttk.Frame(self)
        footer.pack(fill="x", padx=12, pady=(0, 12))
        ttk.Button(footer, text="Закрыть", command=self.destroy).pack(side="right")

# ---------------------------------------------------------------------------
# Окно карты мира
# ---------------------------------------------------------------------------

class MapWindow(tk.Toplevel):
    """
    Граф локаций на Canvas:
      * зелёный узел   — текущая локация героя;
      * синий узел     — посещённая локация;
      * серый узел     — упомянутая, но не посещённая;
      * линии          — связи между локациями.
    Клик по узлу показывает описание и кнопку «Перейти».
    """

    NODE_R = 24
    NODE_R_CURRENT = 28
    EDGE_TARGET = 150
    MARGIN = 55

    def __init__(self, master, store: LocationStore,
                 get_current_location, on_change=None, on_travel=None):
        super().__init__(master)
        self.title("Карта мира")
        self.geometry("820x620")
        self.minsize(640, 480)
        self.store = store
        self.get_current_location = get_current_location
        self.on_change = on_change
        self.on_travel = on_travel
        self._selected_name = None
        self._positions = {}

        top = ttk.Frame(self)
        top.pack(fill="x", padx=8, pady=6)
        ttk.Button(top, text="Экспорт в Markdown",
                   command=self._export_md).pack(side="left", padx=4)
        ttk.Button(top, text="Экспорт в JSON",
                   command=self._export_json).pack(side="left", padx=4)
        ttk.Button(top, text="Обновить",
                   command=self._redraw).pack(side="right", padx=4)
        ttk.Button(top, text="+ Добавить локацию",
                   command=self._add_manual).pack(side="right", padx=4)

        self.canvas = tk.Canvas(self, background="#F7F7F7",
                                highlightthickness=0)
        self.canvas.pack(fill="both", expand=True, padx=8, pady=(0, 4))
        self.canvas.bind("<Button-1>", self._on_click)
        self.canvas.bind("<Configure>", lambda e: self._redraw())

        info = ttk.LabelFrame(self, text="Выбранная локация")
        info.pack(fill="x", padx=8, pady=(0, 8))

        self.info_name = ttk.Label(info, text="(ничего не выбрано)",
                                   font=("TkDefaultFont", 11, "bold"))
        self.info_name.pack(anchor="w", padx=6, pady=(6, 2))
        self.info_desc = ttk.Label(info, text="", foreground="#555",
                                   wraplength=760, justify="left")
        self.info_desc.pack(anchor="w", padx=6)
        self.info_conns = ttk.Label(info, text="", foreground="#555",
                                    wraplength=760, justify="left")
        self.info_conns.pack(anchor="w", padx=6, pady=(2, 4))

        btns = ttk.Frame(info)
        btns.pack(fill="x", padx=6, pady=(0, 6))
        self.btn_travel = ttk.Button(btns, text="Перейти сюда",
                                     command=self._travel_selected,
                                     state="disabled")
        self.btn_travel.pack(side="left")
        ttk.Button(btns, text="Редактировать...",
                   command=self._edit_selected).pack(side="left", padx=6)
        ttk.Button(btns, text="Удалить",
                   command=self._delete_selected).pack(side="left", padx=6)

        self.after(80, self._redraw)

    # -- Отрисовка ---------------------------------------------------------

    def _redraw(self):
        c = self.canvas
        c.delete("all")
        locs = self.store.locations
        W = c.winfo_width() or 800
        H = c.winfo_height() or 400

        if not locs:
            c.create_text(W / 2, H / 2,
                          text="Пока нет локаций.\n"
                               "Они появятся по ходу истории.",
                          fill="#888", font=("TkDefaultFont", 11),
                          justify="center")
            self._positions = {}
            return

        current = self.get_current_location() or ""
        positions = self._compute_layout(locs, W, H)
        self._positions = positions

        # Рёбра (без дублей)
        drawn = set()
        for loc in locs:
            a = loc["name"]
            for cname in loc.get("connections", []):
                key = tuple(sorted([a.lower(), cname.lower()]))
                if key in drawn:
                    continue
                drawn.add(key)
                if cname not in positions:
                    continue
                x1, y1 = positions[a]
                x2, y2 = positions[cname]
                # Пунктирная линия, если хотя бы один конец не посещён
                a_disc = loc.get("discovered", True)
                b_loc = self.store.find(cname)
                b_disc = b_loc.get("discovered", True) if b_loc else True
                if a_disc and b_disc:
                    c.create_line(x1, y1, x2, y2, fill="#9AA", width=2)
                else:
                    c.create_line(x1, y1, x2, y2, fill="#BBB", width=1,
                                  dash=(4, 4))

        # Узлы
        for loc in locs:
            name = loc["name"]
            x, y = positions[name]
            is_current = (name == current)
            is_discovered = loc.get("discovered", True)
            r = self.NODE_R_CURRENT if is_current else self.NODE_R
            if is_current:
                fill, outline, text_fill = "#4CAF50", "#2E7D32", "white"
            elif is_discovered:
                fill, outline, text_fill = "#BBDEFB", "#1976D2", "#111"
            else:
                fill, outline, text_fill = "#ECECEC", "#999", "#666"

            c.create_oval(x - r, y - r, x + r, y + r,
                          fill=fill, outline=outline, width=2,
                          tags=("node", name))
            label = name
            if len(label) > 13:
                label = label[:12] + "…"
            c.create_text(x, y, text=label, fill=text_fill,
                          font=("TkDefaultFont", 9), tags=("node", name))

        self._refresh_info()

    @classmethod
    def _compute_layout(cls, locs, W, H):
        """
        Простой force-directed layout:
          * расталкивание всех пар,
          * притяжение по рёбрам к целевой длине EDGE_TARGET,
          * лёгкая тяга к центру,
          * clamp по границам.
        Стартуем с круга — это даёт предсказуемый результат для малых графов.
        """
        n = len(locs)
        cx, cy = W / 2, H / 2
        init_r = min(W, H) * 0.32
        pos = {}
        for i, loc in enumerate(locs):
            angle = 2 * math.pi * i / max(n, 1) - math.pi / 2
            pos[loc["name"]] = [cx + init_r * math.cos(angle),
                                cy + init_r * math.sin(angle)]

        edges = []
        seen = set()
        for loc in locs:
            a = loc["name"]
            for cname in loc.get("connections", []):
                if cname not in pos:
                    continue
                key = tuple(sorted([a, cname]))
                if key in seen:
                    continue
                seen.add(key)
                edges.append((a, cname))

        if n <= 1:
            return {name: (p[0], p[1]) for name, p in pos.items()}

        names = list(pos.keys())
        iterations = 90
        for _ in range(iterations):
            forces = {nm: [0.0, 0.0] for nm in names}
            # Repulsion
            for i in range(len(names)):
                a = names[i]
                for j in range(i + 1, len(names)):
                    b = names[j]
                    dx = pos[a][0] - pos[b][0]
                    dy = pos[a][1] - pos[b][1]
                    d2 = dx * dx + dy * dy
                    if d2 < 1.0:
                        d2 = 1.0
                    d = math.sqrt(d2)
                    f = 5500.0 / d2
                    fx = (dx / d) * f
                    fy = (dy / d) * f
                    forces[a][0] += fx
                    forces[a][1] += fy
                    forces[b][0] -= fx
                    forces[b][1] -= fy
            # Attraction
            for a, b in edges:
                dx = pos[b][0] - pos[a][0]
                dy = pos[b][1] - pos[a][1]
                d = math.sqrt(dx * dx + dy * dy) + 0.01
                f = (d - cls.EDGE_TARGET) * 0.035
                fx = (dx / d) * f
                fy = (dy / d) * f
                forces[a][0] += fx
                forces[a][1] += fy
                forces[b][0] -= fx
                forces[b][1] -= fy
            # Apply
            damp = 0.45
            for nm, f in forces.items():
                pos[nm][0] += f[0] * damp
                pos[nm][1] += f[1] * damp
            # Centering
            for nm in names:
                pos[nm][0] += (cx - pos[nm][0]) * 0.02
                pos[nm][1] += (cy - pos[nm][1]) * 0.02

        margin = cls.MARGIN
        for nm in names:
            pos[nm][0] = max(margin, min(W - margin, pos[nm][0]))
            pos[nm][1] = max(margin, min(H - margin, pos[nm][1]))

        return {nm: (p[0], p[1]) for nm, p in pos.items()}

    # -- Взаимодействие ----------------------------------------------------

    def _on_click(self, event):
        if not self._positions:
            return
        x, y = event.x, event.y
        best = None
        best_d2 = (self.NODE_R_CURRENT + 8) ** 2
        for name, (nx, ny) in self._positions.items():
            d2 = (nx - x) ** 2 + (ny - y) ** 2
            if d2 < best_d2:
                best = name
                best_d2 = d2
        self._selected_name = best
        self._redraw()

    def _refresh_info(self):
        name = self._selected_name
        if not name:
            self.info_name.configure(text="(ничего не выбрано)")
            self.info_desc.configure(text="")
            self.info_conns.configure(text="")
            self.btn_travel.configure(state="disabled")
            return
        loc = self.store.find(name)
        if loc is None:
            return
        mark = "" if loc.get("discovered", True) else "  [?]"
        self.info_name.configure(text=f"{loc['name']}{mark}")
        self.info_desc.configure(
            text=loc.get("description") or "(без описания)"
        )
        conns = loc.get("connections") or []
        self.info_conns.configure(
            text=("Связано с: " + ", ".join(conns)) if conns else ""
        )
        self.btn_travel.configure(state="normal")

    def _travel_selected(self):
        if not self._selected_name:
            return
        if self.on_travel:
            try:
                self.on_travel(self._selected_name)
            except Exception:
                pass

    def _add_manual(self):
        def _save(new_loc):
            new_loc["discovered"] = True
            res, _ = self.store.update_or_add(new_loc, discovered=True)
            self._redraw()
            if self.on_change:
                try:
                    self.on_change()
                except Exception:
                    pass

        _LocationEditor(self, {"name": "Новая локация",
                               "description": "",
                               "connections": []},
                        all_names=self.store.names(),
                        on_save=_save)

    def _edit_selected(self):
        if not self._selected_name:
            return
        loc = self.store.find(self._selected_name)
        if loc is None:
            return

        def _save(updated):
            # Обновляем на месте
            loc["name"] = updated["name"]
            loc["description"] = updated.get("description", "")
            loc["connections"] = list(updated.get("connections") or [])
            self._selected_name = loc["name"]
            self._redraw()
            if self.on_change:
                try:
                    self.on_change()
                except Exception:
                    pass

        _LocationEditor(self, dict(loc),
                        all_names=self.store.names(),
                        on_save=_save)

    def _delete_selected(self):
        if not self._selected_name:
            return
        loc = self.store.find(self._selected_name)
        if loc is None:
            return
        if not messagebox.askyesno(
            "Удалить локацию",
            f"Удалить «{loc['name']}» с карты?\n"
            "Связи с ней из других локаций тоже удалятся.",
            parent=self,
        ):
            return
        self.store.remove(loc)
        self._selected_name = None
        self._redraw()
        if self.on_change:
            try:
                self.on_change()
            except Exception:
                pass

    # -- Экспорт -----------------------------------------------------------

    def _export_md(self):
        path = filedialog.asksaveasfilename(
            defaultextension=".md",
            filetypes=[("Markdown", "*.md"), ("Все файлы", "*.*")],
        )
        if path:
            self.store.export_markdown(path)
            messagebox.showinfo("Готово", f"Карта экспортирована в {path}")

    def _export_json(self):
        path = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=[("JSON", "*.json"), ("Все файлы", "*.*")],
        )
        if path:
            self.store.export_json(path)
            messagebox.showinfo("Готово", f"Карта экспортирована в {path}")

class _LocationEditor(tk.Toplevel):
    """Небольшой редактор локации для MapWindow."""

    def __init__(self, master, loc: dict, all_names=None, on_save=None):
        super().__init__(master)
        self.title("Локация")
        self.geometry("460x380")
        self.transient(master)
        self.grab_set()
        self.loc = dict(loc)
        self.all_names = [n for n in (all_names or []) if n != loc.get("name")]
        self._on_save = on_save

        frm = ttk.Frame(self)
        frm.pack(fill="both", expand=True, padx=10, pady=10)

        ttk.Label(frm, text="Название:").pack(anchor="w")
        self.name_var = tk.StringVar(value=self.loc.get("name", ""))
        ttk.Entry(frm, textvariable=self.name_var).pack(fill="x")

        ttk.Label(frm, text="Описание:").pack(anchor="w", pady=(6, 0))
        self.desc_text = tk.Text(frm, height=5, wrap="word")
        self.desc_text.insert("1.0", self.loc.get("description", ""))
        self.desc_text.pack(fill="x")

        ttk.Label(
            frm,
            text="Связи (имена соседних локаций через запятую):",
        ).pack(anchor="w", pady=(6, 0))
        self.conns_var = tk.StringVar(
            value=", ".join(self.loc.get("connections") or [])
        )
        ttk.Entry(frm, textvariable=self.conns_var).pack(fill="x")

        if self.all_names:
            ttk.Label(
                frm,
                text="Уже существуют: " + ", ".join(self.all_names[:8]) +
                     ("…" if len(self.all_names) > 8 else ""),
                foreground="#777", wraplength=420, justify="left",
            ).pack(anchor="w", pady=(4, 0))

        btns = ttk.Frame(frm)
        btns.pack(fill="x", pady=10)
        ttk.Button(btns, text="Сохранить", command=self._save).pack(side="right")
        ttk.Button(btns, text="Отмена", command=self.destroy).pack(side="right", padx=6)

    def _save(self):
        name = self.name_var.get().strip() or "Без названия"
        conns = [c.strip() for c in self.conns_var.get().split(",") if c.strip()]
        self.loc["name"] = name
        self.loc["description"] = self.desc_text.get("1.0", "end").strip()
        self.loc["connections"] = conns
        self.destroy()
        if self._on_save:
            self._on_save(self.loc)


# ---------------------------------------------------------------------------
# Главное окно
# ---------------------------------------------------------------------------

class MainApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Text Quest AI — Российская версия")
        self.geometry("880x700")

        self.settings = load_settings()
        self.ai = AIClient(provider=self.settings.text_provider)
        self.ai.set_endpoint_config(self.settings.text_endpoints or {})
        self.save_manager = SaveManager()
        self.card_store = CardStore()
        self.quest_store = QuestStore()
        self.location_store = LocationStore()
        self.current_location = ""
        self.cfg = StoryConfig()
        self.history = []
        self.story_summary = ""
        self.turn_count = 0
        self._last_save_path = None
        self._compressing = False
        self.custom_actions = []
        self.important_facts = []          # редактируемая память сюжета
        self._buffer_before_last_ai = None # снапшот story_buffer для регенерации
        # --- Параметры генерации (глобальные, из AppSettings) ---
        self._base_temperature = float(
            getattr(self.settings, "temperature", DEFAULT_AI_TEMPERATURE)
        )
        self._max_tokens = int(
            getattr(self.settings, "max_tokens", DEFAULT_AI_MAX_TOKENS)
        )
        self._top_p = float(
            getattr(self.settings, "top_p", DEFAULT_AI_TOP_P)
        )
        self._turn_length = str(
            getattr(self.settings, "turn_length", DEFAULT_TURN_LENGTH)
        )
        self.auto_buttons_enabled = tk.BooleanVar(value=True)
        self.auto_speak = tk.BooleanVar(
            value=bool(getattr(self.settings, "auto_speak", False))
        )
        self.voice = VoiceEngine(
            rate=getattr(self.settings, "tts_rate", TTS_RATE_DEFAULT),
            voice_id=getattr(self.settings, "tts_voice", ""),
        )
        self._stt_busy = False
        self._last_narrative = ""
        self.result_queue = queue.Queue()
        self._last_ai_actions = []

        # --- UX: история ввода, анимация «ИИ печатает», отмена ---
        self._input_history = []
        self._input_history_index = None
        self.typing_label = None
        self._typing_animation_id = None
        self._typing_dots = 0
        self._cancel_requested = False

        # --- Логи и статистика ---
        self.app_logger = AppLogger()
        self.stats = SessionStats()

        # --- Плагины ---
        self.plugin_manager = PluginManager(
            mods_dir=MODS_DIR, logger=self.app_logger,
        )
        try:
            self.plugin_manager.load_all()
        except Exception as e:
            try:
                self.app_logger.log_error("plugin", e,
                                          {"context": "load_all"})
            except Exception:
                pass
        # Прокидываем плагинных провайдеров в AI-клиент.
        try:
            self.ai.set_plugin_providers(self.plugin_manager.get_providers())
        except Exception:
            pass

        self.mode = "single"
        self.server = None
        self.client_net = None
        self.player_name = "Хост"
        self.player_role = ROLE_HOST
        self.player_state = PlayerState("Хост")
        self.remote_player_states = {}
        self._pending_actions = []
        self._batch_timer_id = None
        self._is_processing = False
        self._story_buffer = ""
        self._closing = False
        self._auto_roll_chain = 0

        # --- Мультиплеер v2 ---
        self._last_connection = None      # (host, port, name, password)
        self._reconnect_attempts = 0
        self._reconnect_timer_id = None
        self._chat_lines = []             # [(from, text), ...]
        self.private_mode = tk.BooleanVar(value=False)

        # --- Undo/Redo/Ветки ---
        self._undo_stack = []
        self._redo_stack = []
        self._branches = {}                # name -> state dict
        self._pre_action_snapshot = None   # состояние до текущего действия

        self._build_menu()
        self._build_layout()
        self.protocol("WM_DELETE_WINDOW", self._on_close)
        self.bind("<Control-z>", lambda e: self._undo_turn())
        self.bind("<Control-y>", lambda e: self._redo_turn())
        self.bind("<Control-Shift-Z>", lambda e: self._redo_turn())
        self.bind("<Control-r>", lambda e: self._regenerate_last())
        self.bind("<Control-s>", lambda e: self._save_game())
        self.bind("<Control-o>", lambda e: self._load_game())
        self.bind("<Control-Return>", lambda e: self._send_action(
            self.input_var.get()
        ))
        self.bind("<Escape>", lambda e: self._close_topmost())
        # Применяем тему сразу после построения UI.
        try:
            self.after(50, self._apply_theme)
        except tk.TclError:
            pass
        self.after(100, self._poll_queue)
        self.after(200, self._show_startup_choice)

    def _build_menu(self):
        menubar = tk.Menu(self)

        story_menu = tk.Menu(menubar, tearoff=0)
        story_menu.add_command(label="Настроить историю...", command=self.open_setup)
        story_menu.add_command(label="Новая игра (сброс)", command=self.reset_game)
        story_menu.add_separator()
        story_menu.add_command(
            label="Сохранить игру", accelerator="Ctrl+S",
            command=lambda: self._save_game(),
        )
        story_menu.add_command(
            label="Сохранить как...",
            command=lambda: self._save_game(force_dialog=True),
        )
        story_menu.add_command(
            label="Загрузить игру...", accelerator="Ctrl+O",
            command=lambda: self._load_game(),
        )
        story_menu.add_separator()
        self._recent_saves_menu = tk.Menu(
            story_menu, tearoff=0,
            postcommand=self._rebuild_recent_saves_menu,
        )
        story_menu.add_cascade(
            label="Недавние сохранения", menu=self._recent_saves_menu
        )
        story_menu.add_command(
            label="Открыть папку сохранений", command=self._open_saves_folder
        )
        story_menu.add_separator()
        story_menu.add_command(
            label="Отменить ход", accelerator="Ctrl+Z",
            command=self._undo_turn,
        )
        story_menu.add_command(
            label="Вернуть ход", accelerator="Ctrl+Y",
            command=self._redo_turn,
        )
        story_menu.add_separator()
        story_menu.add_command(
            label="Сохранить ветку...", command=self._save_branch,
        )
        story_menu.add_command(
            label="Восстановить ветку...", command=self._restore_branch,
        )
        story_menu.add_separator()
        story_menu.add_command(
            label="Важные факты...", command=self.open_facts,
        )
        story_menu.add_command(
            label="Перегенерировать последний ответ",
            accelerator="Ctrl+R",
            command=self._regenerate_last,
        )
        story_menu.add_separator()
        story_menu.add_command(
            label="Экспорт книги (Markdown)...", command=self.export_book,
        )
        story_menu.add_command(
            label="Статистика сессии...", command=self.open_stats_window,
        )
        story_menu.add_command(
            label="Открыть журнал ошибок", command=self._open_logs_folder,
        )
        story_menu.add_separator()
        story_menu.add_command(
            label="Экспорт книги в PDF...", command=self.export_book_pdf,
        )
        self.dark_theme_var = tk.BooleanVar(
            value=(getattr(self.settings, "theme", "light") == "dark")
        )
        story_menu.add_checkbutton(
            label="Тёмная тема",
            variable=self.dark_theme_var,
            command=self._toggle_theme,
        )
        self.smart_scroll_var = tk.BooleanVar(
            value=bool(getattr(self.settings, "smart_scroll", True))
        )
        story_menu.add_checkbutton(
            label="Умная прокрутка истории",
            variable=self.smart_scroll_var,
            command=self._toggle_smart_scroll,
        )

        self._story_menu = story_menu

        self._story_menu = story_menu

        menubar.add_cascade(label="История", menu=story_menu)

        cards_menu = tk.Menu(menubar, tearoff=0)
        cards_menu.add_command(
            label="Открыть карточки и бестиарий", command=self.open_cards,
        )
        menubar.add_cascade(label="Карточки", menu=cards_menu)

        quest_menu = tk.Menu(menubar, tearoff=0)
        quest_menu.add_command(
            label="Открыть журнал квестов", command=self.open_quests,
        )
        menubar.add_cascade(label="Квесты", menu=quest_menu)

        map_menu = tk.Menu(menubar, tearoff=0)
        map_menu.add_command(
            label="Открыть карту мира", command=self.open_map,
        )
        menubar.add_cascade(label="Карта", menu=map_menu)

        inv_menu = tk.Menu(menubar, tearoff=0)
        inv_menu.add_command(label="Открыть инвентарь и экипировку",
                             command=self.open_inventory)
        inv_menu.add_command(label="Добавить предмет вручную...",
                             command=self.add_item_to_inventory)
        inv_menu.add_separator()
        inv_menu.add_command(label="Характеристики героя...",
                             command=self.open_stats)
        menubar.add_cascade(label="Инвентарь", menu=inv_menu)

        mp_menu = tk.Menu(menubar, tearoff=0)
        mp_menu.add_command(label="Создать игру (хост)...",
                            command=self.open_host_dialog)
        mp_menu.add_command(label="Подключиться к игре...",
                            command=self.open_join_dialog)
        mp_menu.add_separator()
        mp_menu.add_command(label="Роли игроков...",
                            command=self.open_roles_dialog)
        mp_menu.add_command(label="Отключиться / остановить сервер",
                            command=self.stop_multiplayer)
        menubar.add_cascade(label="Сетевая игра", menu=mp_menu)

        plugins_menu = tk.Menu(menubar, tearoff=0)
        plugins_menu.add_command(
            label="Открыть папку модов", command=self.open_mods_folder,
        )
        plugins_menu.add_command(
            label="Перезагрузить плагины", command=self._reload_plugins,
        )
        plugins_menu.add_separator()
        plugins_menu.add_command(
            label="Список загруженных плагинов...",
            command=self.show_loaded_plugins,
        )
        plugins_menu.add_command(
            label="Создать пример плагина (Погода)",
            command=self.create_sample_plugin,
        )
        menubar.add_cascade(label="Плагины", menu=plugins_menu)

        self.config(menu=menubar)
        self._update_undo_menu_state()

    def _build_layout(self):
        text_frame = ttk.Frame(self)
        text_frame.pack(fill="both", expand=True, padx=8, pady=(8, 4))

        self.story_text = tk.Text(
            text_frame, wrap="word", state="disabled", font=("Georgia", 11),
            undo=False,
        )
        # Теги для Markdown.
        self.story_text.tag_configure(
            "md_bold", font=("Georgia", 11, "bold")
        )
        self.story_text.tag_configure(
            "md_italic", font=("Georgia", 11, "italic")
        )
        self.story_text.tag_configure(
            "md_code", font=("Consolas", 10)
        )
        story_scroll = ttk.Scrollbar(text_frame, command=self.story_text.yview)
        self.story_text.configure(yscrollcommand=story_scroll.set)
        self.story_text.pack(side="left", fill="both", expand=True)
        story_scroll.pack(side="right", fill="y")

        mode_frame = ttk.Frame(self)
        mode_frame.pack(fill="x", padx=8)
        ttk.Checkbutton(
            mode_frame,
            text="Автоматические кнопки от ИИ",
            variable=self.auto_buttons_enabled,
        ).pack(side="left")
        ttk.Checkbutton(
            mode_frame,
            text="🔊 Озвучивать ИИ",
            variable=self.auto_speak,
            command=self._on_auto_speak_toggle,
        ).pack(side="left", padx=(12, 0))
        ttk.Button(
            mode_frame, text="+ Добавить свою кнопку",
            command=self._add_custom_action,
        ).pack(side="right")
        ttk.Button(
            mode_frame, text="Очистить свои кнопки",
            command=self._clear_custom_actions,
        ).pack(side="right", padx=6)

        self.buttons_frame = ttk.Frame(self)
        self.buttons_frame.pack(fill="x", padx=8, pady=6)

        # --- Панель чата игроков ---
        self.chat_frame = ttk.LabelFrame(self, text="Чат игроков")
        self.chat_frame.pack(fill="x", padx=8, pady=(0, 4))

        chat_body = ttk.Frame(self.chat_frame)
        chat_body.pack(fill="x", padx=6, pady=(4, 2))

        self.chat_listbox = tk.Listbox(
            chat_body, height=4, font=("Consolas", 9),
            activestyle="none", selectmode="browse",
        )
        chat_scroll = ttk.Scrollbar(
            chat_body, orient="vertical", command=self.chat_listbox.yview,
        )
        self.chat_listbox.configure(yscrollcommand=chat_scroll.set)
        self.chat_listbox.pack(side="left", fill="both", expand=True)
        chat_scroll.pack(side="right", fill="y")

        chat_input_row = ttk.Frame(self.chat_frame)
        chat_input_row.pack(fill="x", padx=6, pady=(0, 6))
        self.chat_input_var = tk.StringVar()
        chat_entry = ttk.Entry(chat_input_row, textvariable=self.chat_input_var)
        chat_entry.pack(side="left", fill="x", expand=True)
        chat_entry.bind("<Return>", lambda e: self._send_chat())
        ttk.Button(
            chat_input_row, text="Отправить в чат",
            command=self._send_chat,
        ).pack(side="left", padx=(6, 0))

        # --- Строка ввода действия ---
        input_frame = ttk.Frame(self)
        input_frame.pack(fill="x", padx=8, pady=(0, 8))
        self.input_var = tk.StringVar()

        # Используем Combobox — он даёт автодополнение истории ввода.
        self.action_entry = ttk.Combobox(
            input_frame, textvariable=self.input_var, values=[],
        )
        self.action_entry.pack(side="left", fill="x", expand=True)
        self.action_entry.bind(
            "<Return>", lambda e: self._send_action(self.input_var.get())
        )
        self.action_entry.bind("<Up>", lambda e: self._on_input_history(-1))
        self.action_entry.bind("<Down>", lambda e: self._on_input_history(1))

        ttk.Checkbutton(
            input_frame, text="Приватно",
            variable=self.private_mode,
        ).pack(side="left", padx=(6, 0))

        # --- Голосовые кнопки ---
        self.mic_btn = ttk.Button(
            input_frame, text="🎤", width=3,
            command=self._toggle_listen,
        )
        self.mic_btn.pack(side="left", padx=(6, 0))

        self.speak_btn = ttk.Button(
            input_frame, text="🔊 Прочитать", width=13,
            command=self._speak_last,
        )
        self.speak_btn.pack(side="left", padx=(4, 0))

        self.stop_speak_btn = ttk.Button(
            input_frame, text="⏹", width=3,
            command=self._stop_speaking,
        )
        self.stop_speak_btn.pack(side="left", padx=(4, 0))

        self.send_btn = ttk.Button(
            input_frame,
            text="Отправить",
            command=lambda: self._send_action(self.input_var.get()),
        )
        self.send_btn.pack(side="left", padx=6)

        self.cancel_ai_btn = ttk.Button(
            input_frame, text="✖ Стоп",
            command=self._cancel_ai_request, state="disabled",
        )
        self.cancel_ai_btn.pack(side="left")

        self.status_var = tk.StringVar(value="Готово.")
        ttk.Label(self, textvariable=self.status_var, foreground="#666").pack(
            fill="x", padx=8
        )

        self.stats_label_var = tk.StringVar(value="")
        self.stats_label = ttk.Label(
            self, textvariable=self.stats_label_var,
            foreground="#888", font=("TkDefaultFont", 9),
        )
        self.stats_label.pack(fill="x", padx=8, pady=(0, 6))

        self._update_stats_label()

    def _show_startup_choice(self):
        dlg = tk.Toplevel(self)
        dlg.title("Режим запуска")
        dlg.geometry("420x230")
        dlg.transient(self)
        dlg.grab_set()
        try:
            dlg.resizable(False, False)
        except tk.TclError:
            pass

        ttk.Label(
            dlg, text="Как запустить игру?",
            font=("TkDefaultFont", 12, "bold"),
        ).pack(pady=(18, 10))

        def choose(mode):
            dlg.destroy()
            if mode == "single":
                self.open_setup()
            elif mode == "host":
                self.open_setup(then_host=True)
            elif mode == "join":
                self.open_join_dialog()

        ttk.Button(
            dlg, text="Одиночная игра", width=40,
            command=lambda: choose("single"),
        ).pack(pady=4)
        ttk.Button(
            dlg, text="Создать сетевую игру (хост)", width=40,
            command=lambda: choose("host"),
        ).pack(pady=4)
        ttk.Button(
            dlg, text="Подключиться к сетевой игре", width=40,
            command=lambda: choose("join"),
        ).pack(pady=4)

    # ---- Сохранение и загрузка ------------------------------------------

    def _build_game_state(self) -> dict:
        """Сериализуемое состояние всей сессии."""
        remote = {}
        for name, st in self.remote_player_states.items():
            try:
                remote[name] = st.to_dict()
            except Exception:
                pass
        return {
            "mode": self.mode,
            "turn_count": int(self.turn_count),
            "cfg": self.cfg.to_dict(),
            "history": list(self.history),
            "story_summary": self.story_summary or "",
            "story_buffer": self._story_buffer or "",
            "cards": [dict(c) for c in self.card_store.cards],
            "quests": [dict(q) for q in self.quest_store.quests],
            "locations": [dict(l) for l in self.location_store.locations],
            "current_location": self.current_location or "",
            "important_facts": list(self.important_facts),
            "stats": self.stats.to_dict(),
            "plugin_state": dict(self.plugin_manager.api.state),
            "player_name": self.player_name,
            "player_state": self.player_state.to_dict(),
            "remote_player_states": remote,
            "custom_actions": list(self.custom_actions),
            "last_ai_actions": list(self._last_ai_actions),
        }

    def _apply_game_state(self, state: dict, reset_network: bool = True):
        """
        Восстанавливает сессию из словаря сохранения или in-memory снапшота.

        reset_network=True  — для загрузки из файла: мультиплеер сбрасывается.
        reset_network=False — для undo/redo и веток: сеть и режим сохраняются.
        """
        # Сетевые соединения не переживают перезапуск — сбрасываем мультиплеер.
        if reset_network and (self.server or self.client_net):
            self.stop_multiplayer()

        # Конфиг истории
        cfg_dict = state.get("cfg") or {}
        try:
            self.cfg = from_dict(cfg_dict)
        except Exception:
            self.cfg = StoryConfig()

        # Счётчики и память
        self.turn_count = int(state.get("turn_count") or 0)
        self.history = [h for h in (state.get("history") or [])
                        if isinstance(h, dict)]
        self.story_summary = state.get("story_summary") or ""
        self._compressing = False

        # Карточки
        self.card_store = CardStore()
        for c in (state.get("cards") or []):
            try:
                self.card_store.add(c)
            except Exception:
                pass

        # Квесты
        self.quest_store = QuestStore()
        for q in (state.get("quests") or []):
            try:
                self.quest_store.add(q, turn_count=self.turn_count)
            except Exception:
                pass

        # Локации и текущая позиция
        self.location_store = LocationStore()
        for loc in (state.get("locations") or []):
            try:
                disc = loc.get("discovered", True)
                self.location_store.add(loc, discovered=disc)
            except Exception:
                pass
        self.current_location = state.get("current_location") or ""
        self.important_facts = [
            str(f).strip()
            for f in (state.get("important_facts") or [])
            if str(f).strip()
        ]
        self.stats = SessionStats.from_dict(state.get("stats") or {})

        # Восстанавливаем состояние плагинов.
        plugin_state = state.get("plugin_state")
        if isinstance(plugin_state, dict):
            try:
                self.plugin_manager.api.state.clear()
                self.plugin_manager.api.state.update(plugin_state)
            except Exception:
                pass

        # Состояние игрока
        self.player_name = str(state.get("player_name") or "Хост")[:30]
        ps_dict = state.get("player_state") or {}
        try:
            self.player_state = PlayerState.from_dict(ps_dict)
        except Exception:
            self.player_state = PlayerState(self.player_name)
        self.player_state.name = self.player_name

        # Состояния других игроков (на случай, если сейв делал хост)
        self.remote_player_states = {}
        for name, st_dict in (state.get("remote_player_states") or {}).items():
            try:
                self.remote_player_states[name] = PlayerState.from_dict(st_dict)
            except Exception:
                pass

        # Кнопки и последние действия ИИ
        self.custom_actions = [str(a) for a in (state.get("custom_actions") or [])]
        self._last_ai_actions = [str(a) for a in (state.get("last_ai_actions") or [])]

        # Сбрасываем недоделанные ходы/таймеры
        if self._batch_timer_id is not None:
            try:
                self.after_cancel(self._batch_timer_id)
            except Exception:
                pass
            self._batch_timer_id = None
        self._pending_actions = []
        self._is_processing = False

        # Восстанавливаем текст повествования
        self._set_story_text(state.get("story_buffer") or "")
        self._render_buttons(self._last_ai_actions)
        self._update_stats_label()

        # Сбрасываем «пре-экшн» снапшот — он относится к прошлому состоянию
        self._pre_action_snapshot = None

        if reset_network:
            self.mode = "single"
            self.title(f"Text Quest AI — {self.cfg.title}")
        # При undo/redo текущий режим (single/host/client) сохраняем —
        # иначе undo в мультиплеере отключил бы сеть.

    def _save_game(self, path: str = None, force_dialog: bool = False,
                   quiet: bool = False):
        """
        Сохраняет игру.
          * path         — конкретный файл.
          * force_dialog — всегда спрашивать имя (пункт «Сохранить как...»).
          * quiet        — без messagebox (для автосейва).
        """
        if path is None and not force_dialog and self._last_save_path:
            # Быстрое сохранение в последний использованный файл
            path = self._last_save_path

        if path is None:
            safe_title = re.sub(r"[^\w\-]+", "_", self.cfg.title)[:40] or "save"
            default_name = f"{safe_title}_{self.turn_count}t.json"
            path = filedialog.asksaveasfilename(
                title="Сохранить игру",
                defaultextension=".json",
                initialfile=default_name,
                initialdir=SAVES_DIR,
                filetypes=[("Сохранение Text Quest", "*.json"),
                           ("Все файлы", "*.*")],
            )
            if not path:
                return None

        # если пользователь выбрал путь без .json — добавим
        if not path.lower().endswith(".json"):
            path += ".json"

        try:
            self.save_manager.save(path, self._build_game_state())
        except Exception as e:
            if not quiet:
                messagebox.showerror("Сохранение",
                                     f"Не удалось сохранить игру:\n{e}")
            return None

        self._last_save_path = path
        if not quiet:
            self.status_var.set(f"Игра сохранена: {os.path.basename(path)}")
            messagebox.showinfo("Сохранение",
                                f"Игра сохранена в файл:\n{path}")
        return path

    def _autosave(self):
        """Тихий автосейв — не открывает диалогов и не показывает ошибок."""
        if not self.history and not self._story_buffer:
            return
        try:
            self.save_manager.autosave(self._build_game_state())
        except Exception:
            pass

    def _load_game(self, path: str = None):
        if path is None:
            path = filedialog.askopenfilename(
                title="Загрузить игру",
                initialdir=SAVES_DIR,
                filetypes=[("Сохранение Text Quest", "*.json"),
                           ("Все файлы", "*.*")],
            )
            if not path:
                return

        if not os.path.isfile(path):
            messagebox.showerror("Загрузка", f"Файл не найден:\n{path}")
            return

        if not messagebox.askyesno(
            "Загрузка",
            "Текущая игра будет заменена загруженной.\nПродолжить?",
        ):
            return

        try:
            state = self.save_manager.load(path)
        except Exception as e:
            messagebox.showerror("Загрузка",
                                 f"Не удалось прочитать файл:\n{e}")
            return

        try:
            self._apply_game_state(state)
        except Exception as e:
            messagebox.showerror("Загрузка",
                                 f"Не удалось применить сохранение:\n{e}")
            return

        self._last_save_path = path
        self._clear_undo_history()
        messagebox.showinfo(
            "Загрузка",
            f"Игра «{self.cfg.title}» загружена.\n"
            f"Ход: {self.turn_count}. Карточек: {len(self.card_store.cards)}.",
        )

    def _rebuild_recent_saves_menu(self):
        """Перестраивает подменю «Недавние сохранения» перед показом."""
        menu = getattr(self, "_recent_saves_menu", None)
        if menu is None:
            return
        menu.delete(0, "end")

        saves = self.save_manager.list_saves()
        if not saves:
            menu.add_command(label="(нет сохранений)", state="disabled")
        else:
            for meta in saves[:RECENT_SAVES_COUNT]:
                title = meta.get("title") or meta["name"]
                tc = meta.get("turn_count")
                suffix = f"  —  ход {tc}" if isinstance(tc, int) else ""
                label = f"{title}{suffix}"
                if len(label) > 64:
                    label = label[:61] + "…"
                path = meta["path"]
                menu.add_command(
                    label=label,
                    command=lambda p=path: self._load_game(p),
                )

        menu.add_separator()
        menu.add_command(label="Загрузить из файла...",
                         command=lambda: self._load_game())
        menu.add_command(label="Открыть папку сохранений",
                         command=self._open_saves_folder)

    def _open_saves_folder(self):
        try:
            webbrowser.open("file://" + SAVES_DIR)
        except Exception as e:
            messagebox.showerror("Ошибка",
                                 f"Не удалось открыть папку:\n{e}")

    def _open_logs_folder(self):
        try:
            webbrowser.open("file://" + LOGS_DIR)
        except Exception as e:
            messagebox.showerror("Ошибка",
                                 f"Не удалось открыть папку:\n{e}")

    # ---- Плагины --------------------------------------------------------

    def open_mods_folder(self):
        try:
            webbrowser.open("file://" + MODS_DIR)
        except Exception as e:
            messagebox.showerror("Ошибка",
                                 f"Не удалось открыть папку:\n{e}")

    def _reload_plugins(self):
        if self._is_processing:
            messagebox.showinfo(
                "Плагины",
                "Дождитесь ответа ИИ — сейчас нельзя перезагрузить плагины.",
            )
            return
        try:
            self.plugin_manager.reload()
        except Exception as e:
            self.app_logger.log_error("plugin", e, {"context": "reload"})
            messagebox.showerror("Плагины",
                                 f"Ошибка перезагрузки:\n{e}")
            return
        # Обновляем провайдеров в AI-клиенте.
        try:
            self.ai.set_plugin_providers(self.plugin_manager.get_providers())
        except Exception:
            pass

        loaded = self.plugin_manager.loaded
        errors = self.plugin_manager.errors
        text = [f"Загружено плагинов: {len(loaded)}."]
        if loaded:
            for fname, label in loaded:
                text.append(f"  – {label}  ({fname})")
        if errors:
            text.append("")
            text.append(f"Ошибок: {len(errors)}")
            for fname, err in errors:
                text.append(f"  – {fname}: {err}")
        messagebox.showinfo("Плагины", "\n".join(text))
        self.status_var.set(
            f"Плагины перезагружены: {len(loaded)} шт., ошибок: {len(errors)}."
        )

    def show_loaded_plugins(self):
        text = self.plugin_manager.summary()
        messagebox.showinfo("Плагины", text, parent=self)

    def create_sample_plugin(self):
        target = os.path.join(MODS_DIR, "weather.py")
        if os.path.exists(target):
            if not messagebox.askyesno(
                "Плагины",
                f"Файл уже существует:\n{target}\n\nПерезаписать?",
            ):
                return
        try:
            with open(target, "w", encoding="utf-8") as f:
                f.write(SAMPLE_WEATHER_PLUGIN)
        except Exception as e:
            messagebox.showerror("Плагины",
                                 f"Не удалось создать файл:\n{e}")
            return
        messagebox.showinfo(
            "Плагины",
            f"Пример создан:\n{target}\n\n"
            "Нажмите «Плагины → Перезагрузить плагины», чтобы "
            "активировать его без перезапуска игры.",
        )

    def _build_plugin_context(self, plugin_data: dict = None) -> dict:
        """
        Собирает контекст, который получают prompt- и turn-end-хуки.
        Все ключи — JSON-совместимые.
        """
        try:
            eff_stats = self.player_state.get_effective_stats() or {}
        except Exception:
            eff_stats = {}
        try:
            inv_names = [
                (it.get("name") or "?") for it in self.player_state.inventory
            ]
        except Exception:
            inv_names = []
        try:
            active_quests = [
                {"name": q.get("name"), "description": q.get("description")}
                for q in self.quest_store.active()
            ]
        except Exception:
            active_quests = []

        return {
            "api": self.plugin_manager.api,
            "turn_count": int(self.turn_count),
            "current_location": self.current_location or "",
            "player_name": self.player_name,
            "player_stats": dict(eff_stats),
            "inventory_names": inv_names,
            "quests_active": active_quests,
            "plugin_data": dict(plugin_data or {}),
        }

    # ---- UX: горячие клавиши --------------------------------------------

    def _close_topmost(self):
        """Escape: закрыть верхнее модальное окно, если оно есть."""
        try:
            for w in self.winfo_children():
                if isinstance(w, tk.Toplevel) and w.winfo_exists() \
                        and w.winfo_viewable():
                    try:
                        w.destroy()
                    except tk.TclError:
                        pass
        except tk.TclError:
            pass

    # ---- UX: история ввода ----------------------------------------------

    def _remember_input(self, text: str):
        text = (text or "").strip()
        if not text:
            return
        if self._input_history and self._input_history[-1] == text:
            self._input_history_index = None
            return
        self._input_history.append(text)
        if len(self._input_history) > INPUT_HISTORY_LIMIT:
            self._input_history.pop(0)
        self._input_history_index = None
        try:
            self.action_entry.configure(values=list(self._input_history))
        except (AttributeError, tk.TclError):
            pass

    def _on_input_history(self, direction: int):
        if not self._input_history:
            return "break"
        if self._input_history_index is None:
            self._input_history_index = len(self._input_history)
        self._input_history_index += direction
        if self._input_history_index < 0:
            self._input_history_index = 0
        if self._input_history_index >= len(self._input_history):
            self._input_history_index = len(self._input_history)
            self.input_var.set("")
            return "break"
        try:
            self.input_var.set(self._input_history[self._input_history_index])
            self.action_entry.icursor("end")
        except (AttributeError, tk.TclError):
            pass
        return "break"

    # ---- UX: анимация «ИИ печатает» ------------------------------------

    def _start_typing_animation(self, label_widget):
        self._stop_typing_animation()
        self.typing_label = label_widget
        self._typing_dots = 0
        self._tick_typing()

    def _stop_typing_animation(self):
        if self._typing_animation_id is not None:
            try:
                self.after_cancel(self._typing_animation_id)
            except Exception:
                pass
            self._typing_animation_id = None
        self.typing_label = None

    def _tick_typing(self):
        if not self._is_processing:
            self._typing_animation_id = None
            return
        dots = "·" * (1 + (self._typing_dots % 3))
        lbl = self.typing_label
        if lbl is not None:
            try:
                if lbl.winfo_exists():
                    lbl.configure(text=f"ИИ печатает {dots}")
            except tk.TclError:
                pass
        self._typing_dots += 1
        self._typing_animation_id = self.after(TYPING_TICK_MS, self._tick_typing)

    # ---- UX: отмена запроса --------------------------------------------

    def _cancel_ai_request(self):
        if not self._is_processing:
            return
        self._cancel_requested = True
        self.status_var.set("Запрос отменён (ждём завершения сетевой операции).")

    # ---- UX: тема -------------------------------------------------------

    def _toggle_theme(self):
        theme = "dark" if self.dark_theme_var.get() else "light"
        self.settings.theme = theme
        try:
            save_settings(self.settings)
        except Exception:
            pass
        self._apply_theme()

    def _toggle_smart_scroll(self):
        self.settings.smart_scroll = bool(self.smart_scroll_var.get())
        try:
            save_settings(self.settings)
        except Exception:
            pass
        self.status_var.set(
            "Умная прокрутка включена." if self.settings.smart_scroll
            else "Автопрокрутка к концу при новом сообщении."
        )

    def _apply_theme(self):
        """Применяет текущую палитру ко всем ключевым виджетам."""
        theme = getattr(self.settings, "theme", "light")
        palette = THEMES.get(theme, THEMES["light"])

        try:
            style = ttk.Style(self)
            try:
                style.theme_use("clam")
            except tk.TclError:
                pass

            bg = palette["bg"]
            fg = palette["fg"]

            style.configure(".", background=bg, foreground=fg)
            for cls in ("TFrame", "TLabel", "TButton", "TCheckbutton",
                        "TRadiobutton", "TLabelframe", "TLabelframe.Label",
                        "TNotebook", "TNotebook.Tab", "TPanedwindow"):
                style.configure(cls, background=bg, foreground=fg)
            style.map("TButton",
                      background=[("active", palette["story_sel"])])
            style.map("TCheckbutton", background=[("active", bg)])
            style.map("TRadiobutton", background=[("active", bg)])
            style.configure("TEntry",
                            fieldbackground=palette["story_bg"],
                            foreground=palette["story_fg"])
            style.configure("TCombobox",
                            fieldbackground=palette["story_bg"],
                            foreground=palette["story_fg"])
            style.configure("TScale", background=bg)
        except tk.TclError:
            pass

        try:
            self.configure(bg=palette["bg"])
        except tk.TclError:
            pass

        for widget in (getattr(self, "story_text", None),
                       getattr(self, "chat_listbox", None)):
            if widget is None:
                continue
            try:
                widget.configure(bg=palette["story_bg" if widget is self.story_text
                                          else "chat_bg"],
                                 fg=palette["story_fg" if widget is self.story_text
                                            else "chat_fg"],
                                 insertbackground=palette["story_fg"])
            except tk.TclError:
                pass

        # Перекрашиваем статусные метки и одиночные ttk.Label с явным цветом.
        try:
            self.stats_label.configure(foreground=palette["stats_fg"])
        except (AttributeError, tk.TclError):
            pass

    # ---- UX: умная прокрутка -------------------------------------------

    def _is_story_at_bottom(self) -> bool:
        try:
            return self.story_text.yview()[1] >= 0.999
        except tk.TclError:
            return True

    # ---- UX: PDF-экспорт ------------------------------------------------

    def export_book_pdf(self):
        if not self.history and not self._story_buffer:
            messagebox.showinfo("PDF", "Пока нечего экспортировать.")
            return
        try:
            from reportlab.lib.pagesizes import A4
            from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
            from reportlab.lib.units import cm
            from reportlab.platypus import (
                SimpleDocTemplate, Paragraph, Spacer, PageBreak,
            )
        except ImportError:
            messagebox.showinfo(
                "PDF",
                "Для экспорта в PDF установите библиотеку:\n\n"
                "    pip install reportlab",
            )
            return

        safe_title = re.sub(r"[^\w\-]+", "_", self.cfg.title)[:40] or "book"
        default_name = f"{safe_title}_book.pdf"
        path = filedialog.asksaveasfilename(
            title="Экспорт книги в PDF",
            defaultextension=".pdf",
            initialfile=default_name,
            initialdir=SAVES_DIR,
            filetypes=[("PDF", "*.pdf"), ("Все файлы", "*.*")],
        )
        if not path:
            return

        try:
            self._write_book_pdf(path, A4, Paragraph, ParagraphStyle,
                                 SimpleDocTemplate, Spacer, PageBreak, cm,
                                 getSampleStyleSheet)
        except Exception as e:
            self.app_logger.log_error(
                "ui", e, {"context": "export_book_pdf", "path": path},
            )
            messagebox.showerror("PDF",
                                 f"Не удалось сохранить PDF:\n{e}")
            return
        self.status_var.set(f"PDF сохранён: {os.path.basename(path)}")
        messagebox.showinfo("PDF", f"PDF сохранён в файл:\n{path}")

    def _write_book_pdf(self, path, A4, Paragraph, ParagraphStyle,
                        SimpleDocTemplate, Spacer, PageBreak, cm,
                        getSampleStyleSheet):
        styles = getSampleStyleSheet()
        h1 = ParagraphStyle(
            "H1x", parent=styles["Heading1"], fontSize=18, spaceAfter=12,
        )
        h2 = ParagraphStyle(
            "H2x", parent=styles["Heading2"], fontSize=14, spaceAfter=10,
        )
        body = ParagraphStyle(
            "Body", parent=styles["BodyText"], fontSize=11, leading=15,
        )
        quote = ParagraphStyle(
            "Quote", parent=body, leftIndent=18, textColor="#555555",
            fontSize=10,
        )

        def _esc(s: str) -> str:
            return (s or "").replace("&", "&amp;").replace("<", "&lt;") \
                           .replace(">", "&gt;")

        doc = SimpleDocTemplate(
            path, pagesize=A4,
            leftMargin=2 * cm, rightMargin=2 * cm,
            topMargin=2 * cm, bottomMargin=2 * cm,
            title=self.cfg.title, author="Text Quest AI",
        )
        flow = []
        flow.append(Paragraph(_esc(self.cfg.title), h1))
        flow.append(Paragraph(
            _esc(f"Жанр: {self.cfg.genre}"), body,
        ))
        flow.append(Paragraph(
            _esc(f"Герой: {self.cfg.hero_name} — {self.cfg.hero_desc}"), body,
        ))
        flow.append(Paragraph(_esc(f"Ходов: {self.turn_count}"), body))
        flow.append(Spacer(1, 12))

        if self.story_summary:
            flow.append(Paragraph("Краткое содержание", h2))
            flow.append(Paragraph(_esc(self.story_summary), body))
            flow.append(PageBreak())

        chapter = 0
        pending_user = []
        for entry in self.history:
            if not isinstance(entry, dict):
                continue
            role = entry.get("role")
            content = entry.get("content") or ""
            if role == "user":
                t = content.strip()
                if t and t != "Начни историю.":
                    pending_user.append(t)
                continue
            if role != "assistant":
                continue

            chapter += 1
            flow.append(Paragraph(f"Глава {chapter}", h2))

            for msg in pending_user:
                flow.append(Paragraph(
                    "&gt; " + _esc(msg.replace("\n", " ")), quote,
                ))
            pending_user = []
            flow.append(Spacer(1, 6))

            try:
                (narrative, actions, cards,
                 quests, rolls, locations, _pd) = parse_ai_response(content)
            except Exception:
                narrative, actions, cards = content, [], []
                quests, rolls, locations = [], [], []

            for para in (narrative or "").split("\n\n"):
                para = para.strip()
                if para:
                    flow.append(Paragraph(_esc(para), body))
                    flow.append(Spacer(1, 6))

            if rolls:
                flow.append(Paragraph("Проверки", h2))
                for r in rolls:
                    stat = r.get("stat", "?")
                    dc = r.get("dc", "?")
                    label = (r.get("label") or "").strip()
                    line = f"{stat} против {dc}"
                    if label:
                        line = f"{label}: {line}"
                    flow.append(Paragraph("• " + _esc(line), body))
                flow.append(Spacer(1, 6))

            if cards:
                flow.append(Paragraph("Новые карточки", h2))
                for c in cards:
                    nm = c.get("name", "?")
                    tp = c.get("type", "предмет")
                    de = (c.get("description") or "").strip()
                    line = f"<b>{_esc(nm)}</b> ({_esc(tp)})"
                    if de:
                        line += f" — {_esc(de)}"
                    flow.append(Paragraph(line, body))
                flow.append(Spacer(1, 6))

            if actions:
                flow.append(Paragraph("Возможные действия", h2))
                for a in actions:
                    flow.append(Paragraph("• " + _esc(a), body))
                flow.append(Spacer(1, 6))

            flow.append(Spacer(1, 12))

        if self.important_facts:
            flow.append(Paragraph("Важные факты", h2))
            for i, f in enumerate(self.important_facts, 1):
                flow.append(Paragraph(f"{i}. {_esc(f)}", body))
            flow.append(Spacer(1, 12))

        if self.quest_store.quests:
            flow.append(Paragraph("Журнал квестов", h2))
            for q in self.quest_store.quests:
                nm = q.get("name", "?")
                st = QUEST_STATUS_LABELS.get(q.get("status"), "?")
                de = (q.get("description") or "").strip()
                line = f"<b>{_esc(nm)}</b> [{_esc(st)}]"
                if de:
                    line += f" — {_esc(de)}"
                flow.append(Paragraph(line, body))

        doc.build(flow)

    def _update_stats_label(self):
        s = self.stats
        if s.tokens_reports:
            tokens_part = (
                f"Токены: {_fmt_num(s.tokens_in)} / {_fmt_num(s.tokens_out)}"
            )
            currency, cost = s.estimate_cost(self.settings.text_provider)
            if currency and currency != "—":
                tokens_part += f"  (~{cost:.4f} {currency})"
        else:
            tokens_part = "Токены: — (провайдер не вернул usage)"

        text = (
            f"Ходы: {s.turns}  |  "
            f"Символы: {_fmt_num(s.chars_in)} / {_fmt_num(s.chars_out)}  |  "
            f"{tokens_part}"
        )
        if s.errors:
            text += f"  |  Ошибок: {s.errors}"
        try:
            self.stats_label_var.set(text)
        except (AttributeError, tk.TclError):
            pass

    def open_stats_window(self):
        SessionStatsWindow(self, self.stats, self.settings.text_provider)

    def export_book(self):
        """Экспортирует сессию в Markdown-файл с главами по ходам."""
        if not self.history and not self._story_buffer:
            messagebox.showinfo("Экспорт книги",
                                "Пока нечего экспортировать.")
            return
        safe_title = re.sub(r"[^\w\-]+", "_", self.cfg.title)[:40] or "book"
        default_name = f"{safe_title}_book.md"
        path = filedialog.asksaveasfilename(
            title="Экспорт книги",
            defaultextension=".md",
            initialfile=default_name,
            initialdir=SAVES_DIR,
            filetypes=[("Markdown", "*.md"), ("Все файлы", "*.*")],
        )
        if not path:
            return
        try:
            self._write_book_markdown(path)
        except Exception as e:
            self.app_logger.log_error(
                "ui", e, {"context": "export_book", "path": path},
            )
            messagebox.showerror("Экспорт книги",
                                 f"Не удалось сохранить книгу:\n{e}")
            return
        self.status_var.set(f"Книга сохранена: {os.path.basename(path)}")
        messagebox.showinfo("Экспорт книги",
                            f"Книга сохранена в файл:\n{path}")

    def _write_book_markdown(self, path: str):
        lines = []
        lines.append(f"# {self.cfg.title}")
        lines.append("")
        lines.append(f"*Жанр: {self.cfg.genre}*  ")
        lines.append(
            f"*Герой: {self.cfg.hero_name} — {self.cfg.hero_desc}*  "
        )
        lines.append(f"*Ходов: {self.turn_count}*")
        lines.append("")
        lines.append("---")
        lines.append("")

        if self.story_summary:
            lines.append("## Краткое содержание предыдущих событий")
            lines.append("")
            lines.append(self.story_summary)
            lines.append("")
            lines.append("---")
            lines.append("")

        chapter = 0
        pending_user = []
        for entry in self.history:
            if not isinstance(entry, dict):
                continue
            role = entry.get("role")
            content = entry.get("content") or ""
            if role == "user":
                text = content.strip()
                if text and text != "Начни историю.":
                    pending_user.append(text)
            elif role == "assistant":
                chapter += 1
                lines.append(f"## Глава {chapter}")
                lines.append("")

                if pending_user:
                    lines.append("**Действия игрока:**")
                    lines.append("")
                    for msg in pending_user:
                        for ln in msg.split("\n"):
                            lines.append(f"> {ln}")
                    lines.append("")
                    pending_user = []

                try:
                    (narrative, actions, cards,
                     quests, rolls, locations, _pd) = parse_ai_response(content)
                except Exception:
                    narrative, actions, cards = content, [], []
                    quests, rolls, locations = [], [], []

                if narrative:
                    lines.append(narrative)
                    lines.append("")
                elif actions or cards:
                    lines.append("_(без текстового повествования)_")
                    lines.append("")

                if rolls:
                    lines.append("**Проверки:**")
                    lines.append("")
                    for r in rolls:
                        stat = r.get("stat", "?")
                        dc = r.get("dc", "?")
                        label = (r.get("label") or "").strip()
                        if label:
                            lines.append(f"- {label}: {stat} против {dc}")
                        else:
                            lines.append(f"- {stat} против {dc}")
                    lines.append("")

                if cards:
                    lines.append("**Новые карточки:**")
                    lines.append("")
                    for c in cards:
                        name = c.get("name", "?")
                        ctype = c.get("type", "предмет")
                        desc = (c.get("description") or "").strip()
                        if desc:
                            lines.append(f"- **{name}** _({ctype})_ — {desc}")
                        else:
                            lines.append(f"- **{name}** _({ctype})_")
                    lines.append("")

                if quests:
                    lines.append("**Новые квесты:**")
                    lines.append("")
                    for q in quests:
                        name = q.get("name", "?")
                        qs = QUEST_STATUS_LABELS.get(
                            q.get("status"), q.get("status") or "?"
                        )
                        desc = (q.get("description") or "").strip()
                        if desc:
                            lines.append(f"- **{name}** _({qs})_ — {desc}")
                        else:
                            lines.append(f"- **{name}** _({qs})_")
                    lines.append("")

                if actions:
                    lines.append("**Возможные действия:**")
                    lines.append("")
                    for a in actions:
                        lines.append(f"- {a}")
                    lines.append("")

                lines.append("---")
                lines.append("")

        if self.important_facts:
            lines.append("## Важные факты")
            lines.append("")
            for i, f in enumerate(self.important_facts, 1):
                lines.append(f"{i}. {f}")
            lines.append("")
            lines.append("---")
            lines.append("")

        if self.card_store.cards:
            lines.append("## Мир — предметы и существа")
            lines.append("")
            for c in self.card_store.cards:
                name = c.get("name", "?")
                ctype = c.get("type", "")
                desc = (c.get("description") or "").strip()
                lines.append(f"### {name} _({ctype})_")
                lines.append("")
                meta_bits = []
                if c.get("status"):
                    meta_bits.append(f"статус: {c['status']}")
                if c.get("attitude"):
                    meta_bits.append(f"отношение: {c['attitude']}")
                if c.get("hp") not in (None, ""):
                    meta_bits.append(f"HP: {c['hp']}")
                if c.get("location"):
                    meta_bits.append(f"локация: {c['location']}")
                if meta_bits:
                    lines.append("_" + "; ".join(meta_bits) + "_")
                    lines.append("")
                if desc:
                    lines.append(desc)
                    lines.append("")
                if c.get("character"):
                    lines.append(f"**Характер:** {c['character']}")
                    lines.append("")
                if c.get("goal"):
                    lines.append(f"**Цель:** {c['goal']}")
                    lines.append("")
                props = c.get("properties") or {}
                if props:
                    lines.append("**Свойства:**")
                    lines.append("")
                    for k, v in props.items():
                        lines.append(f"- **{k}**: {v}")
                    lines.append("")
            lines.append("---")
            lines.append("")

        if self.quest_store.quests:
            lines.append("## Журнал квестов")
            lines.append("")
            groups = [
                ("Активные", self.quest_store.by_status("active")),
                ("Выполненные", self.quest_store.by_status("done")),
                ("Проваленные", self.quest_store.by_status("failed")),
            ]
            for title, group in groups:
                if not group:
                    continue
                lines.append(f"### {title}")
                lines.append("")
                for q in group:
                    name = q.get("name", "?")
                    desc = (q.get("description") or "").strip()
                    if desc:
                        lines.append(f"- **{name}** — {desc}")
                    else:
                        lines.append(f"- **{name}**")
                lines.append("")
            lines.append("---")
            lines.append("")

        lines.append("_Книга сгенерирована Text Quest AI_")
        lines.append("")

        with open(path, "w", encoding="utf-8") as f:
            f.write("\n".join(lines))

    # ---- Undo / Redo -----------------------------------------------------

    def _snapshot_state(self) -> dict:
        """
        In-memory снапшот состояния для undo/redo/веток.
        Отличается от save-game только тем, что не пишется на диск.
        """
        return self._build_game_state()

    def _push_undo(self, state: dict):
        self._undo_stack.append(state)
        if len(self._undo_stack) > UNDO_STACK_LIMIT:
            self._undo_stack.pop(0)
        # Новый ход «отрезает» redo-ветку — это стандартная семантика.
        self._redo_stack.clear()
        self._update_undo_menu_state()

    def _update_undo_menu_state(self):
        menu = getattr(self, "_story_menu", None)
        if menu is None:
            return
        try:
            menu.entryconfig(
                "Отменить ход",
                state=("normal" if self._undo_stack else "disabled"),
            )
            menu.entryconfig(
                "Вернуть ход",
                state=("normal" if self._redo_stack else "disabled"),
            )
            menu.entryconfig(
                "Сохранить ветку...",
                state=("normal" if (self._story_buffer or self.history)
                       else "disabled"),
            )
            menu.entryconfig(
                "Восстановить ветку...",
                state=("normal" if self._branches else "disabled"),
            )
            menu.entryconfig(
                "Перегенерировать последний ответ",
                state=("normal"
                       if (self.history
                           and self.history[-1].get("role") == "assistant"
                           and not self._is_processing)
                       else "disabled"),
            )
        except tk.TclError:
            # Меню могло быть уничтожено при закрытии окна
            pass

    def _restore_snapshot(self, state: dict):
        """Применяет снапшот без сброса сети и без диалогов."""
        try:
            self._apply_game_state(state, reset_network=False)
        except Exception as e:
            messagebox.showerror("Откат",
                                 f"Не удалось восстановить состояние:\n{e}")
            return
        self._update_undo_menu_state()

    def _undo_turn(self):
        if not self._undo_stack:
            return
        if self._is_processing or self._pending_actions:
            messagebox.showinfo(
                "Отмена хода",
                "Дождитесь ответа ИИ — сейчас нельзя откатить ход.",
            )
            return

        current = self._snapshot_state()
        prev = self._undo_stack.pop()
        self._redo_stack.append(current)
        self._restore_snapshot(prev)
        self.status_var.set(
            f"Ход отменён. Доступно отмен: {len(self._undo_stack)}, "
            f"возвратов: {len(self._redo_stack)}."
        )

    def _redo_turn(self):
        if not self._redo_stack:
            return
        if self._is_processing or self._pending_actions:
            messagebox.showinfo(
                "Возврат хода",
                "Дождитесь ответа ИИ — сейчас нельзя вернуть ход.",
            )
            return

        current = self._snapshot_state()
        nxt = self._redo_stack.pop()
        self._undo_stack.append(nxt)
        if len(self._undo_stack) > UNDO_STACK_LIMIT:
            self._undo_stack.pop(0)
        self._restore_snapshot(current)
        self.status_var.set(
            f"Ход возвращён. Доступно отмен: {len(self._undo_stack)}, "
            f"возвратов: {len(self._redo_stack)}."
        )

    def _regenerate_last(self):
        """Удаляет последний ответ ИИ и запрашивает заново с temp + delta."""
        if self._is_processing or self._pending_actions:
            messagebox.showinfo(
                "Регенерация",
                "Дождитесь ответа ИИ — сейчас нельзя перегенерировать.",
            )
            return
        if self.mode == "client":
            messagebox.showinfo(
                "Регенерация",
                "Перегенерировать может только хост или игрок в одиночной игре.",
            )
            return
        if not self.history or self.history[-1].get("role") != "assistant":
            messagebox.showinfo(
                "Регенерация",
                "Нет ответа ИИ для перегенерации.",
            )
            return

        # 1. Убираем последний ответ ИИ из истории.
        self.history.pop()

        # 2. Возвращаем story_buffer к состоянию до ответа.
        if self._buffer_before_last_ai is not None:
            self._set_story_text(self._buffer_before_last_ai)

        # 3. Откатываем счётчик хода.
        if self.turn_count > 0:
            self.turn_count -= 1

        # 4. Новый запрос — user-сообщение уже в истории, не дублируем.
        new_temp = min(1.5, self._base_temperature + REGEN_TEMPERATURE_DELTA)
        self.status_var.set(
            f"Перегенерация (temperature {new_temp:.2f})..."
        )
        self._send_to_ai(
            user_message="",
            multiplayer=(self.mode == "host"),
            temperature=new_temp,
            append_user=False,
            push_undo=False,
        )

    def _clear_undo_history(self):
        self._undo_stack.clear()
        self._redo_stack.clear()
        self._pre_action_snapshot = None
        self._update_undo_menu_state()

    # ---- Ветки -----------------------------------------------------------

    def _save_branch(self):
        if not self._story_buffer and not self.history:
            messagebox.showinfo("Ветки", "Пока нечего сохранять.")
            return

        default_name = f"Ветка {len(self._branches) + 1}"
        name = simpledialog.askstring(
            "Сохранить ветку",
            "Имя ветки (можно вернуться к ней позже в этой сессии):",
            initialvalue=default_name,
            parent=self,
        )
        if not name:
            return
        name = name.strip()
        if not name:
            return

        if name in self._branches:
            if not messagebox.askyesno(
                "Ветки",
                f"Ветка «{name}» уже существует. Перезаписать её?",
            ):
                return

        self._branches[name] = self._snapshot_state()
        self._update_undo_menu_state()
        self.status_var.set(
            f"Ветка «{name}» сохранена. Всего веток: {len(self._branches)}."
        )

    def _restore_branch(self):
        if not self._branches:
            messagebox.showinfo("Ветки", "Нет сохранённых веток.")
            return
        if self._is_processing or self._pending_actions:
            messagebox.showinfo(
                "Ветки",
                "Дождитесь ответа ИИ — сейчас нельзя переключить ветку.",
            )
            return

        dlg = tk.Toplevel(self)
        dlg.title("Восстановить ветку")
        dlg.geometry("460x360")
        dlg.transient(self)
        dlg.grab_set()

        ttk.Label(
            dlg, text="Выберите ветку для восстановления:",
            font=("TkDefaultFont", 11, "bold"),
        ).pack(pady=(12, 6))

        info = ttk.Label(
            dlg, text="", foreground="#666", wraplength=420, justify="left",
        )
        info.pack(fill="x", padx=12, pady=(0, 4))

        listbox = tk.Listbox(dlg, font=("Consolas", 10), activestyle="dotbox")
        listbox.pack(fill="both", expand=True, padx=12, pady=6)

        names = sorted(self._branches.keys())
        for nm in names:
            listbox.insert("end", nm)
        if names:
            listbox.selection_set(0)

        def _update_info(_e=None):
            sel = listbox.curselection()
            if not sel:
                info.configure(text="")
                return
            nm = names[int(sel[0])]
            st = self._branches.get(nm) or {}
            tc = st.get("turn_count", "?")
            cards = len(st.get("cards") or [])
            info.configure(
                text=f"Ход: {tc}; карточек: {cards}; "
                     f"длина повествования: {len(st.get('story_buffer') or '')} симв."
            )

        listbox.bind("<<ListboxSelect>>", _update_info)
        _update_info()

        btns = ttk.Frame(dlg)
        btns.pack(fill="x", padx=12, pady=(0, 12))

        def _do_restore():
            sel = listbox.curselection()
            if not sel:
                return
            nm = names[int(sel[0])]
            if not messagebox.askyesno(
                "Восстановить ветку",
                f"Текущее состояние заменится веткой «{nm}».\n"
                "Продолжить? (текущий ход можно будет вернуть через "
                "«Вернуть ход»)",
                parent=dlg,
            ):
                return
            state = self._branches.get(nm)
            dlg.destroy()
            if state is None:
                return
            # Текущее состояние в redo, ветку — в undo.
            self._redo_stack.append(self._snapshot_state())
            self._undo_stack.append(state)
            if len(self._undo_stack) > UNDO_STACK_LIMIT:
                self._undo_stack.pop(0)
            self._restore_snapshot(state)
            self.status_var.set(f"Восстановлена ветка «{nm}».")

        def _do_delete():
            sel = listbox.curselection()
            if not sel:
                return
            nm = names[int(sel[0])]
            if not messagebox.askyesno(
                "Удалить ветку", f"Удалить ветку «{nm}»?", parent=dlg,
            ):
                return
            self._branches.pop(nm, None)
            listbox.delete(int(sel[0]))
            names.pop(int(sel[0]))
            if names:
                listbox.selection_set(0)
            _update_info()
            self._update_undo_menu_state()

        ttk.Button(btns, text="Восстановить", command=_do_restore).pack(
            side="right", padx=4
        )
        ttk.Button(btns, text="Удалить", command=_do_delete).pack(
            side="right", padx=4
        )
        ttk.Button(btns, text="Отмена", command=dlg.destroy).pack(
            side="right", padx=4
        )

    def open_setup(self, then_host=False):
        if self.mode == "client":
            messagebox.showinfo(
                "Сетевая игра",
                "Вы подключены как клиент — историю настраивает хост.",
            )
            return
        SetupDialog(
            self, self.cfg, self.settings,
            lambda cfg, s: self._start_story(cfg, s, then_host=then_host),
        )

    def _start_story(self, cfg: StoryConfig, settings: AppSettings,
                     then_host: bool = False):
        self.cfg = cfg
        self.settings = settings
        self.ai.set_provider(settings.text_provider)
        self.ai.set_key_pool(settings.text_key_pool)
        self.ai.set_endpoint_config(settings.text_endpoints or {})

        # Обновляем локальные копии параметров генерации.
        self._base_temperature = float(
            getattr(settings, "temperature", DEFAULT_AI_TEMPERATURE)
        )
        self._max_tokens = int(
            getattr(settings, "max_tokens", DEFAULT_AI_MAX_TOKENS)
        )
        self._top_p = float(
            getattr(settings, "top_p", DEFAULT_AI_TOP_P)
        )
        self._turn_length = str(
            getattr(settings, "turn_length", DEFAULT_TURN_LENGTH)
        )

        self.history = []
        self.story_summary = ""
        self.turn_count = 0
        self._compressing = False
        self.card_store = CardStore()
        self.quest_store = QuestStore()
        self.location_store = LocationStore()
        self.current_location = ""
        self.important_facts = []
        self._buffer_before_last_ai = None
        self.custom_actions = []
        self.stats = SessionStats()
        self._update_stats_label()
        self._pending_actions = []
        self._is_processing = False
        initial_stats = cfg.base_stats or DEFAULT_STATS
        self.player_state = PlayerState(self.player_name, stats=initial_stats)
        self.remote_player_states = {}
        self._last_save_path = None
        self._auto_roll_chain = 0
        self._clear_undo_history()
        self._branches = {}
        if self._batch_timer_id is not None:
            try:
                self.after_cancel(self._batch_timer_id)
            except Exception:
                pass
            self._batch_timer_id = None

        self._set_story_text("")
        self._append_story(f"=== {cfg.title} ===")

        if self.mode == "host" and self.server:
            self.server.broadcast({"type": "reset", "cfg": cfg.to_dict()})

        self._send_to_ai(
            user_message="Начни историю.",
            is_start=True,
            multiplayer=(self.mode == "host"),
        )

        if then_host:
            self.after(200, self.open_host_dialog)

    def reset_game(self):
        if self.mode == "client":
            messagebox.showinfo(
                "Сетевая игра",
                "Сброс истории доступен только хосту.",
            )
            return
        if messagebox.askyesno(
            "Новая игра", "Начать заново с текущими настройками истории?"
        ):
            self._start_story(self.cfg, self.settings)

    def open_inventory(self):
        InventoryWindow(
            self, self.player_state,
            on_change=self._on_inventory_changed,
        )

    def open_stats(self):
        StatsWindow(
            self, self.player_state,
            on_change=self._on_inventory_changed,
        )

    def add_item_to_inventory(self):
        def _save(new_item):
            self.player_state.add_item(new_item)
            self.status_var.set(
                f"В рюкзак добавлено: {new_item.get('name', '?')}"
            )
            self._on_inventory_changed()

        ItemEditor(
            self,
            {"name": "Новый предмет", "type": "предмет",
             "description": "", "properties": {}},
            on_save=_save,
        )

    def _on_inventory_changed(self):
        if self.mode == "client" and self.client_net:
            try:
                self.client_net.send({
                    "type": "player_state",
                    "state": self.player_state.to_dict(),
                })
            except Exception:
                pass

    def open_cards(self):
        CardsWindow(
            self, self.card_store,
            player_state=self.player_state,
            on_inventory_change=self._on_inventory_changed,
        )

    def open_quests(self):
        def _on_change():
            # Если мы хост — рассылаем клиентам актуальный журнал.
            if self.mode == "host" and self.server:
                self.server.broadcast({
                    "type": "quests",
                    "quests": [dict(q) for q in self.quest_store.quests],
                })

        QuestWindow(self, self.quest_store, on_change=_on_change)

    def open_map(self):
        def _on_change():
            if self.mode == "host" and self.server:
                self.server.broadcast({
                    "type": "locations",
                    "locations": [dict(l) for l in self.location_store.locations],
                })

        def _on_travel(name):
            self._send_action(f"Иду в {name}")

        MapWindow(
            self, self.location_store,
            get_current_location=lambda: self.current_location,
            on_change=_on_change,
            on_travel=_on_travel,
        )

    def open_facts(self):
        def _save(new_list):
            self.important_facts = [
                str(f).strip() for f in (new_list or []) if str(f).strip()
            ]
            self.status_var.set(
                f"Важные факты сохранены ({len(self.important_facts)})."
            )
            if self.mode == "host" and self.server:
                self.server.broadcast({
                    "type": "facts",
                    "facts": list(self.important_facts),
                })

        FactsWindow(self, list(self.important_facts), on_save=_save)

    def open_roles_dialog(self):
        if self.mode != "host" or not self.server:
            messagebox.showinfo("Роли игроков",
                                "Управлять ролями может только хост.")
            return

        mapping = self.server.player_roles()
        # Хост свою роль не меняет
        editable = {n: r for n, r in mapping.items()
                    if n != self.player_name}

        dlg = tk.Toplevel(self)
        dlg.title("Роли игроков")
        dlg.geometry("440x380")
        dlg.transient(self)
        dlg.grab_set()

        ttk.Label(
            dlg, text="Назначьте роли подключённым игрокам:",
            font=("TkDefaultFont", 11, "bold"),
        ).pack(anchor="w", padx=12, pady=(12, 6))

        body = ttk.Frame(dlg)
        body.pack(fill="both", expand=True, padx=12, pady=(0, 8))

        roles_reverse = list(ROLE_LABELS.keys())
        role_labels = [ROLE_LABELS[r] for r in roles_reverse]
        vars_ = {}

        if not editable:
            ttk.Label(
                body, text="Пока никто не подключился.",
                foreground="#777",
            ).pack(anchor="w")
        else:
            for i, (name, role) in enumerate(sorted(editable.items())):
                row = ttk.Frame(body)
                row.pack(fill="x", pady=4)
                ttk.Label(row, text=name, width=20,
                          anchor="w").pack(side="left")
                var = tk.StringVar(value=ROLE_LABELS.get(role, "игрок"))
                cb = ttk.Combobox(row, textvariable=var, state="readonly",
                                  values=role_labels, width=16)
                cb.pack(side="left", padx=6)
                vars_[name] = var

        def _apply():
            for name, var in vars_.items():
                label = var.get()
                for rid, rlabel in ROLE_LABELS.items():
                    if rlabel == label:
                        self.server.set_role_by_name(name, rid)
                        break
            dlg.destroy()
            self.status_var.set("Роли обновлены.")

        btns = ttk.Frame(dlg)
        btns.pack(fill="x", padx=12, pady=(0, 12))
        ttk.Button(btns, text="Применить", command=_apply).pack(side="right")
        ttk.Button(btns, text="Отмена",
                   command=dlg.destroy).pack(side="right", padx=6)

    def open_host_dialog(self):
        if self.mode == "client":
            messagebox.showinfo("Сетевая игра",
                                "Сначала отключитесь от текущей игры.")
            return
        if self.server:
            messagebox.showinfo("Сетевая игра", "Сервер уже запущен.")
            return

        name = simpledialog.askstring(
            "Хост", "Ваше имя в игре:", initialvalue=self.player_name, parent=self
        )
        if not name:
            return
        port = simpledialog.askinteger(
            "Хост", "Порт для подключения:", initialvalue=DEFAULT_MP_PORT,
            minvalue=1024, maxvalue=65535, parent=self,
        )
        if not port:
            return
        password = simpledialog.askstring(
            "Хост", "Пароль (можно оставить пустым):", parent=self, show="*"
        )
        if password is None:
            password = ""

        self.player_name = (name.strip() or "Хост")[:30]
        self.player_state.name = self.player_name
        try:
            self.server = GameServer(self, port, password)
        except OSError as e:
            self.server = None
            messagebox.showerror("Сетевая игра",
                                 f"Не удалось занять порт {port}:\n{e}")
            return

        self.mode = "host"
        try:
            local_ip = socket.gethostbyname(socket.gethostname())
        except OSError:
            local_ip = "127.0.0.1"
        self.title(f"Text Quest AI — Хост ({self.player_name})")
        self._append_story(
            f"*** Сетевой режим: вы — хост. Порт {port}. "
            f"Подключение: {local_ip}:{port} ***"
        )
        messagebox.showinfo(
            "Сетевая игра",
            "Сервер запущен.\n\n"
            f"Ваш IP: {local_ip}\nПорт: {port}\n"
            f"Пароль: {'(нет)' if not password else '(задан)'}\n\n"
            "Сообщите эти данные другим игрокам, чтобы они могли подключиться.\n"
            "Роли игроков можно назначать через меню «Сетевая игра» → "
            "«Роли игроков...».",
        )

    def open_join_dialog(self):
        if self.mode == "host":
            messagebox.showinfo("Сетевая игра",
                                "Сначала остановите свой сервер.")
            return
        if self.client_net:
            messagebox.showinfo("Сетевая игра", "Уже подключено.")
            return

        host = simpledialog.askstring(
            "Подключение", "IP-адрес или имя хоста:", parent=self
        )
        if not host:
            return
        port = simpledialog.askinteger(
            "Подключение", "Порт:", initialvalue=DEFAULT_MP_PORT,
            minvalue=1, maxvalue=65535, parent=self,
        )
        if not port:
            return
        name = simpledialog.askstring(
            "Подключение", "Ваше имя:",
            initialvalue=self.player_name, parent=self,
        )
        if not name:
            return
        password = simpledialog.askstring(
            "Подключение", "Пароль (если задан):", parent=self, show="*"
        )
        if password is None:
            password = ""

        self.player_name = (name.strip() or "Игрок")[:30]
        self.player_state.name = self.player_name
        try:
            self.client_net = ClientNetwork(
                host=host.strip(),
                port=port,
                name=self.player_name,
                password=password,
                on_message=lambda m: self.result_queue.put(("client_message", m)),
                on_disconnect=self._on_client_disconnected,
            )
        except OSError as e:
            self.client_net = None
            messagebox.showerror("Сетевая игра",
                                 f"Не удалось подключиться к {host}:{port}:\n{e}")
            return

        self.mode = "client"
        self.player_role = ROLE_PLAYER
        self._last_connection = (host.strip(), int(port),
                                 self.player_name, password)
        self._reconnect_attempts = 0
        self._set_story_text("")
        self._append_story(
            f"*** Подключение к {host}:{port} как {self.player_name} ***"
        )
        self.status_var.set("Подключено. Ожидание снимка истории...")
        self.title(f"Text Quest AI — Клиент ({self.player_name})")

    def stop_multiplayer(self):
        was_client = self.mode == "client"
        if self.server:
            self.server.stop()
            self.server = None
        if self.client_net:
            try:
                self.client_net.close()
            except Exception:
                pass
            self.client_net = None
        if self._batch_timer_id is not None:
            try:
                self.after_cancel(self._batch_timer_id)
            except Exception:
                pass
            self._batch_timer_id = None
        if self._reconnect_timer_id is not None:
            try:
                self.after_cancel(self._reconnect_timer_id)
            except Exception:
                pass
            self._reconnect_timer_id = None
        self._last_connection = None
        self._reconnect_attempts = 0
        self._pending_actions = []
        self.player_role = ROLE_HOST if not was_client else ROLE_PLAYER
        self.mode = "single"
        self.title("Text Quest AI — Российская версия")
        self._update_input_enabled_state()
        if was_client:
            self.status_var.set("Отключено от хоста.")
        else:
            self.status_var.set("Сетевая игра остановлена.")

    def get_sync_snapshot(self) -> dict:
        try:
            players = (self.server.player_names() if self.server else []) + \
                      [self.player_name]
            roles = (self.server.player_roles() if self.server else
                     {self.player_name: ROLE_HOST})
        except Exception:
            players = [self.player_name]
            roles = {self.player_name: ROLE_HOST}
        return {
            "type": "sync",
            "cfg": self.cfg.to_dict(),
            "story": self._story_buffer,
            "cards": list(self.card_store.cards),
            "quests": list(self.quest_store.quests),
            "locations": list(self.location_store.locations),
            "current_location": self.current_location or "",
            "important_facts": list(self.important_facts),
            "actions": list(self._last_ai_actions),
            "players": players,
            "roles": roles,
        }

    def _add_custom_action(self):
        text = simpledialog.askstring(
            "Своя кнопка", "Текст действия для новой кнопки:", parent=self
        )
        if text:
            text = text.strip()
            if text:
                self.custom_actions.append(text)
                self._render_buttons(self._last_ai_actions)

    def _clear_custom_actions(self):
        self.custom_actions = []
        self._render_buttons(self._last_ai_actions)

    # ---- Голос: ввод ----------------------------------------------------

    def _toggle_listen(self):
        """Кнопка 🎤: записать короткую фразу и распознать её."""
        if self._stt_busy:
            self.status_var.set("Уже слушаю — дождитесь результата.")
            return

        ok, msg = _check_stt_available()
        if not ok:
            self.status_var.set(msg)
            return

        self._stt_busy = True
        try:
            self.mic_btn.configure(text="…", state="disabled")
        except tk.TclError:
            pass
        self.status_var.set("Слушаю...")

        def _on_result(text):
            self.after(0, lambda t=text: self._on_stt_result(t))

        def _on_error(err):
            self.after(0, lambda e=err: self._on_stt_error(e))

        def _on_status(st):
            self.after(0, lambda s=st: self.status_var.set(s))

        threading.Thread(
            target=_listen_and_recognize,
            args=(_on_result, _on_error, _on_status),
            daemon=True,
            name="STTWorker",
        ).start()

    def _on_stt_result(self, text):
        self._stt_busy = False
        try:
            self.mic_btn.configure(text="🎤", state="normal")
        except tk.TclError:
            return
        if text:
            self.input_var.set(text)
            self.status_var.set(f"Распознано: {text}")
        else:
            self.status_var.set("Речь не распознана.")

    def _on_stt_error(self, msg):
        self._stt_busy = False
        try:
            self.mic_btn.configure(text="🎤", state="normal")
        except tk.TclError:
            return
        self.status_var.set(msg)

    # ---- Голос: вывод ---------------------------------------------------

    def _on_auto_speak_toggle(self):
        """Пользователь включил/выключил автоозвучку — сохраняем настройку."""
        enabled = bool(self.auto_speak.get())
        self.settings.auto_speak = enabled
        try:
            save_settings(self.settings)
        except Exception:
            pass

        if enabled and not self.voice.is_available():
            err = self.voice.last_error() or "pyttsx3 недоступен."
            self.status_var.set(f"Озвучка выключена: {err}")
            self.auto_speak.set(False)
            self.settings.auto_speak = False
            try:
                save_settings(self.settings)
            except Exception:
                pass
            return

        self.status_var.set(
            "Автоозвучка включена." if enabled else "Автоозвучка выключена."
        )

    def _speak_last(self):
        """Кнопка «🔊 Прочитать»: озвучить последний ответ ИИ."""
        text = (self._last_narrative or "").strip()
        if not text:
            # Fallback — последний абзац повествования
            text = (self._story_buffer or "").strip()[-800:]
        if not text:
            self.status_var.set("Нечего озвучивать.")
            return

        if not self.voice.is_available():
            err = self.voice.last_error() or "pyttsx3 недоступен."
            self.status_var.set(err)
            return

        self.voice.say(text)
        self.status_var.set("Озвучиваю...")

    def _stop_speaking(self):
        """Сброс очереди озвучки — текущая фраза доигрывается."""
        self.voice.stop_current()
        self.status_var.set("Очередь озвучки очищена.")

    # ---- Чат игроков ---------------------------------------------------

    def _append_chat(self, from_name: str, text: str,
                     system: bool = False):
        """Добавляет строку в локальную панель чата."""
        self._chat_lines.append((from_name, text))
        if len(self._chat_lines) > 200:
            self._chat_lines = self._chat_lines[-200:]
            try:
                self.chat_listbox.delete(0, "end")
                for f, t in self._chat_lines:
                    self.chat_listbox.insert("end", self._format_chat(f, t))
            except tk.TclError:
                return
        try:
            self.chat_listbox.insert("end", self._format_chat(from_name, text))
            self.chat_listbox.see("end")
        except tk.TclError:
            pass

    @staticmethod
    def _format_chat(from_name: str, text: str) -> str:
        prefix = f"[{from_name}]" if from_name else "***"
        return f"{prefix} {text}"

    def _send_chat(self):
        text = (self.chat_input_var.get() or "").strip()
        if not text:
            return
        self.chat_input_var.set("")

        if self.mode == "single":
            # В одиночной игре чат бессмыслен, но пусть будет «заметка игрока».
            self._append_chat(self.player_name, text)
            return

        if self.mode == "host":
            # Хост видит свой текст сразу, остальным — через broadcast.
            self._append_chat(self.player_name, text)
            if self.server:
                self.server.broadcast({
                    "type": "chat",
                    "from": self.player_name,
                    "text": text,
                })
            return

        if self.mode == "client":
            if self.client_net and self.client_net.is_alive():
                self._append_chat(self.player_name, text)
                self.client_net.send({"type": "chat", "text": text})
            else:
                self.status_var.set("Нет соединения с хостом.")

    def _on_chat_received(self, from_name: str, text: str):
        self._append_chat(from_name, text)

    # ---- Роли ----------------------------------------------------------

    def _apply_roles(self, mapping: dict):
        """
        mapping: {name: role}. Обновляет роль локального игрока и
        блокирует/разблокирует ввод для наблюдателя.
        """
        if not isinstance(mapping, dict):
            return
        my_role = mapping.get(self.player_name)
        if my_role:
            self.player_role = my_role
        self._update_input_enabled_state()
        if my_role == ROLE_OBSERVER and self.mode == "client":
            self.status_var.set("Ваша роль: наблюдатель — действия недоступны.")

    def _update_input_enabled_state(self):
        """Включает/выключает поле ввода действий по роли."""
        is_observer = (self.player_role == ROLE_OBSERVER
                       and self.mode == "client")
        state = "disabled" if is_observer else "normal"

        for widget in (getattr(self, "action_entry", None),
                       getattr(self, "send_btn", None),
                       getattr(self, "mic_btn", None)):
            if widget is None:
                continue
            try:
                widget.configure(state=state)
            except tk.TclError:
                pass

        # Кнопки действий — они точно ttk.Button, никаких догадок
        for btn in getattr(self, "_action_buttons", ()):
            try:
                btn.configure(state=state)
            except tk.TclError:
                pass

    # ---- Переподключение ------------------------------------------------

    def _schedule_reconnect(self):
        """Планирует попытку переподключения с экспоненциальной задержкой."""
        if not self._last_connection:
            return
        if self._reconnect_timer_id is not None:
            return
        if self._reconnect_attempts >= RECONNECT_MAX_ATTEMPTS:
            self.status_var.set("Переподключение не удалось — работаем оффлайн.")
            self._last_connection = None
            return

        delay = min(
            RECONNECT_BASE_DELAY_MS * (2 ** self._reconnect_attempts),
            RECONNECT_MAX_DELAY_MS,
        )
        self._reconnect_attempts += 1
        self.status_var.set(
            f"Соединение потеряно. Попытка {self._reconnect_attempts}/"
            f"{RECONNECT_MAX_ATTEMPTS} через {delay // 1000} с..."
        )
        self._reconnect_timer_id = self.after(
            delay, self._try_reconnect
        )

    def _try_reconnect(self):
        self._reconnect_timer_id = None
        if self._closing or not self._last_connection:
            return

        host, port, name, password = self._last_connection
        try:
            net = ClientNetwork(
                host=host, port=port, name=name, password=password,
                on_message=lambda m: self.result_queue.put(
                    ("client_message", m)
                ),
                on_disconnect=self._on_client_disconnected,
            )
        except OSError as e:
            self.status_var.set(f"Переподключение не удалось: {e}")
            self._schedule_reconnect()
            return

        # Старое соединение уже мертво — подменяем
        old = self.client_net
        self.client_net = net
        if old is not None and old is not net:
            try:
                old.close()
            except Exception:
                pass
        self._reconnect_attempts = 0
        self.mode = "client"
        self.status_var.set("Переподключено, синхронизация...")

    def _on_client_disconnected(self):
        """Колбэк от ClientNetwork — вызывается из фонового потока."""
        self.result_queue.put(("network_error", "Соединение с хостом потеряно."))

    def _render_buttons(self, ai_actions):
        self._last_ai_actions = list(ai_actions) if ai_actions else []
        self._action_buttons = []
        for w in self.buttons_frame.winfo_children():
            w.destroy()

        actions = []
        if self.auto_buttons_enabled.get():
            actions.extend(self._last_ai_actions)
        actions.extend(self.custom_actions)

        if not actions:
            ttk.Label(
                self.buttons_frame,
                text="(нет доступных кнопок — используйте поле ввода ниже)",
            ).pack(anchor="w")
            return

        row = ttk.Frame(self.buttons_frame)
        row.pack(fill="x")
        col_count = 0
        for action in actions:
            b = ttk.Button(
                row, text=action, command=lambda a=action: self._send_action(a)
            )
            b.pack(side="left", padx=4, pady=4)
            self._action_buttons.append(b)   # <-- добавить
            col_count += 1
            if col_count % 4 == 0:
                row = ttk.Frame(self.buttons_frame)
                row.pack(fill="x")

    def _send_action(self, text):
        text = (text or "").strip()
        if not text:
            return
        self.input_var.set("")
        self._input_history_index = None
        self._remember_input(text)

        if self.mode == "client":
            is_private = bool(self.private_mode.get())
            self._append_story(
                f"> {text}" + (" (приватно)" if is_private else "")
            )
            if self.client_net and self.client_net.is_alive():
                self.client_net.send({
                    "type": "action",
                    "text": text,
                    "private": is_private,
                })
            else:
                self.status_var.set("Нет соединения с хостом.")
            return

        # Новое действие игрока всегда сбрасывает счётчик авто-бросков.
        self._auto_roll_chain = 0

        is_private = bool(self.private_mode.get())

        if self.mode == "host" or self.server:
            self._queue_action(self.player_name, text, is_local=True,
                               is_private=is_private)
        else:
            # Одиночная игра: приватность не имеет смысла, но пометим
            # в промпте, чтобы ИИ мог отреагировать отдельно.
            if self._pre_action_snapshot is None:
                self._pre_action_snapshot = self._snapshot_state()
            label = " (приватно)" if is_private else ""
            self._append_story(f"> {text}{label}")
            user_msg = (f"{self.player_name} (приватно): {text}"
                        if is_private else text)
            self._send_to_ai(user_message=user_msg)

    # ---- Батчинг ----

    def _queue_action(self, player_name: str, text: str, is_local: bool,
                      is_private: bool = False):
        text = text.strip()
        if not text:
            return
        if self._pre_action_snapshot is None:
            self._pre_action_snapshot = self._snapshot_state()
        self._pending_actions.append((player_name, text, is_private))

        suffix = " (приватно)" if is_private else ""
        if is_local:
            self._append_story(f"> {player_name}: {text}{suffix}")
        else:
            tag = " (сеть)" if not is_private else " (сеть, приватно)"
            self._append_story(f"> {player_name}{tag}: {text}")

        names = ", ".join(n for n, _ in self._pending_actions)
        self.status_var.set(
            f"Собрано ходов: {len(self._pending_actions)} ({names}). "
            f"Отправка через {ACTION_BATCH_WINDOW_MS // 1000} с..."
        )

        if self._is_processing:
            return
        if self._batch_timer_id is None:
            self._batch_timer_id = self.after(
                ACTION_BATCH_WINDOW_MS, self._flush_batch
            )

    def _flush_batch(self):
        self._batch_timer_id = None
        if self._is_processing:
            return
        if not self._pending_actions:
            return

        batch = self._pending_actions
        self._pending_actions = []

        lines = []
        for entry in batch:
            if len(entry) == 3:
                name, text, is_priv = entry
            else:
                name, text = entry
                is_priv = False
            if is_priv:
                lines.append(f"{name} (приватно): {text}")
            else:
                lines.append(f"{name}: {text}")
        user_message = "\n".join(lines)
        self._send_to_ai(user_message=user_message, multiplayer=True)

    # ---- Общение с ИИ ----

    def _send_to_ai(self, user_message: str, is_start: bool = False,
                    multiplayer: bool = False,
                    temperature: float = None,
                    append_user: bool = True,
                    push_undo: bool = True,
                    max_tokens: int = None,
                    top_p: float = None):
        # Пушим снапшот «до хода» — на нём будет строиться undo.
        # При старте истории и при регенерации откатывать нечего.
        if push_undo and not is_start and self._pre_action_snapshot is not None:
            self._push_undo(self._pre_action_snapshot)
        self._pre_action_snapshot = None

        self._is_processing = True
        self._cancel_requested = False
        key_label = self.ai.current_key_label()
        status = "ИИ думает..."
        if temperature is not None and abs(
                float(temperature) - self._base_temperature) > 1e-6:
            status = f"ИИ думает (T={float(temperature):.2f})..."
        if key_label:
            status += f" ({key_label})"
        self.status_var.set(status)

        try:
            self.cancel_ai_btn.configure(state="normal")
        except (AttributeError, tk.TclError):
            pass

        for w in self.buttons_frame.winfo_children():
            w.destroy()
        placeholder = ttk.Label(self.buttons_frame, text="ИИ печатает ·")
        placeholder.pack(anchor="w")
        self._start_typing_animation(placeholder)

        if append_user and user_message:
            self.history.append({"role": "user", "content": user_message})

        # Сохраняем снапшот story_buffer для возможной регенерации
        # (в нём ещё нет ответа ИИ — только реплика игрока).
        self._buffer_before_last_ai = self._story_buffer

        use_mp = multiplayer or (self.mode == "host")
        other_players = self.remote_player_states if self.mode == "host" else {}
        plugin_context = self._build_plugin_context()
        plugin_hooks = self.plugin_manager.get_prompt_hooks()
        system_prompt = build_system_prompt(
            self.cfg, self.story_summary, multiplayer=use_mp,
            player_state=self.player_state,
            other_players=other_players,
            quest_store=self.quest_store,
            location_store=self.location_store,
            current_location=self.current_location,
            card_store=self.card_store,
            important_facts=self.important_facts,
            turn_length=self._turn_length,
            plugin_prompt_hooks=plugin_hooks,
            plugin_context=plugin_context,
        )
        history_copy = list(self.history)
        temp = (self._base_temperature if temperature is None
                else float(temperature))
        mt = int(max_tokens if max_tokens is not None else self._max_tokens)
        tp = float(top_p if top_p is not None else self._top_p)
        provider_id = self.ai.provider
        user_msg_for_stats = user_message if append_user else ""

        def worker():
            try:
                reply, usage = self.ai.get_response_with_usage(
                    system_prompt, history_copy,
                    temperature=temp, max_tokens=mt, top_p=tp,
                )
                if self._cancel_requested:
                    self.result_queue.put(("cancelled", None))
                    return
                self.result_queue.put((
                    "ok",
                    {
                        "text": reply or "",
                        "usage": usage or {},
                        "user_message": user_msg_for_stats,
                    },
                ))
            except Exception as e:
                if self._cancel_requested:
                    self.result_queue.put(("cancelled", None))
                    return
                # Логируем с полным трейсбеком и последним промптом.
                try:
                    self.app_logger.log_error(
                        "ai", e,
                        {
                            "provider": provider_id,
                            "temperature": temp,
                            "max_tokens": mt,
                            "top_p": tp,
                            "history_turns": len(history_copy),
                            "prompt": system_prompt,
                        },
                    )
                except Exception:
                    pass
                self.result_queue.put(("error", str(e)))

        threading.Thread(target=worker, daemon=True).start()

    def _poll_queue(self):
        try:
            while True:
                kind, payload = self.result_queue.get_nowait()

                if kind == "ok":
                    self._handle_ai_reply(payload)
                elif kind == "cancelled":
                    self._is_processing = False
                    self._stop_typing_animation()
                    try:
                        self.cancel_ai_btn.configure(state="disabled")
                    except (AttributeError, tk.TclError):
                        pass
                    self._render_buttons(self._last_ai_actions)
                    self.status_var.set("Запрос отменён.")
                elif kind == "summary":
                    self._handle_summary_result(payload)
                elif kind == "summary_error":
                    self._compressing = False
                elif kind == "error":
                    self._is_processing = False
                    self._stop_typing_animation()
                    try:
                        self.cancel_ai_btn.configure(state="disabled")
                    except (AttributeError, tk.TclError):
                        pass
                    self.stats.errors += 1
                    self._update_stats_label()
                    self.status_var.set(
                        "Ошибка. Подробности — в журнале (История → "
                        "Открыть журнал ошибок)."
                    )
                    messagebox.showerror("Ошибка запроса к ИИ", payload)
                elif kind == "player_joined":
                    self.status_var.set(f"Игрок подключился: {payload}")
                    self._append_story(f"*** {payload} присоединился к игре ***")
                    self._broadcast_players()
                    if self.server:
                        self.server.broadcast({
                            "type": "player_state",
                            "state": self.player_state.to_dict(),
                        })
                elif kind == "player_left":
                    self.status_var.set(f"Игрок отключился: {payload}")
                    self._append_story(f"*** {payload} покинул игру ***")
                    self._broadcast_players()
                elif kind == "remote_action":
                    if len(payload) == 3:
                        name, text, is_priv = payload
                    else:
                        name, text = payload
                        is_priv = False
                    self._queue_action(name, text, is_local=False,
                                       is_private=is_priv)
                elif kind == "chat_message":
                    name, text = payload
                    self._on_chat_received(name, text)
                elif kind == "remote_player_state":
                    name, state = payload
                    try:
                        self.remote_player_states[name] = PlayerState.from_dict(state)
                    except Exception:
                        pass
                elif kind == "client_message":
                    self._handle_client_message(payload)
                elif kind == "network_error":
                    self.status_var.set(payload)
                    self._append_story(f"*** {payload} ***")
                    if self.client_net:
                        try:
                            self.client_net.close()
                        except Exception:
                            pass
                        self.client_net = None
                    # Пытаемся переподключиться, если есть куда.
                    if self._last_connection:
                        self._schedule_reconnect()
                    else:
                        self.mode = "single"
                else:
                    self.status_var.set("Неизвестное сообщение очереди.")
        except queue.Empty:
            pass
        if not self._closing:
            self.after(120, self._poll_queue)

    def _broadcast_players(self):
        if self.mode != "host" or not self.server:
            return
        try:
            players = self.server.player_names() + [self.player_name]
        except Exception:
            players = [self.player_name]
        self.server.broadcast({"type": "players", "players": players})

    def _handle_client_message(self, msg: dict):
        if not isinstance(msg, dict):
            return
        mtype = msg.get("type")

        if mtype == "sync":
            cfg_dict = msg.get("cfg") or {}
            try:
                self.cfg = from_dict(cfg_dict)
            except Exception:
                pass
            self._set_story_text(msg.get("story") or "")
            self._story_buffer = msg.get("story") or ""
            self.card_store = CardStore()
            for c in (msg.get("cards") or []):
                try:
                    self.card_store.add(c)
                except Exception:
                    pass
            self.quest_store = QuestStore()
            for q in (msg.get("quests") or []):
                try:
                    self.quest_store.add(q)
                except Exception:
                    pass
            self.location_store = LocationStore()
            for loc in (msg.get("locations") or []):
                try:
                    self.location_store.add(loc)
                except Exception:
                    pass
            self.current_location = msg.get("current_location") or ""
            self.important_facts = [
                str(f).strip()
                for f in (msg.get("important_facts") or [])
                if str(f).strip()
            ]
            self._render_buttons(msg.get("actions") or [])
            players = msg.get("players") or []
            roles = msg.get("roles") or {}
            if roles:
                self._apply_roles(roles)
            self.status_var.set(
                "Синхронизировано. Игроков в игре: "
                f"{len(players)} ({', '.join(players)})"
            )

        elif mtype == "narrative":
            text = (msg.get("text") or "").strip()
            if text:
                self._append_story(text)



        elif mtype == "cards":

            added = []

            updated = []

            for c in (msg.get("cards") or []):

                try:

                    res, action = self.card_store.update_or_add(c)

                except Exception:

                    continue

                if res is None:
                    continue

                if action == "added":

                    added.append(res["name"])

                elif action == "updated":

                    updated.append(res["name"])

            parts = []

            if added:
                parts.append("новые: " + ", ".join(added))

            if updated:
                parts.append("обновлены: " + ", ".join(updated))

            if parts:
                self.status_var.set("Карточки — " + "; ".join(parts))


        elif mtype == "quests":

            added = []

            updated = []

            for q in (msg.get("quests") or []):

                try:

                    res, action = self.quest_store.update_or_add(q)

                except Exception:

                    continue

                if res is None:
                    continue

                if action == "added":

                    added.append(res["name"])

                elif action == "updated":

                    updated.append(res["name"])

            parts = []

            if added:
                parts.append("новые: " + ", ".join(added))

            if updated:
                parts.append("обновлены: " + ", ".join(updated))

            if parts:
                self.status_var.set("Квесты — " + "; ".join(parts))



        elif mtype == "locations":

            added, updated = [], []

            for loc in (msg.get("locations") or []):

                try:

                    res, action = self.location_store.update_or_add(loc)

                except Exception:

                    continue

                if res is None:
                    continue

                (added if action == "added" else updated).append(res["name"])

            parts = []

            if added:
                parts.append("новые: " + ", ".join(added))

            if updated:
                parts.append("обновлены: " + ", ".join(updated))

            if parts:
                self.status_var.set("Карта — " + "; ".join(parts))


        elif mtype == "current_location":

            name = msg.get("name") or ""

            if name:
                self.current_location = name

                self.status_var.set(f"Локация героя: {name}")



        elif mtype == "chat":

            frm = msg.get("from") or "?"

            text = (msg.get("text") or "").strip()

            if text:
                self._on_chat_received(frm, text)


        elif mtype == "roles":

            self._apply_roles(msg.get("roles") or {})

        elif mtype == "facts":
            incoming = msg.get("facts") or []
            self.important_facts = [
                str(f).strip() for f in incoming if str(f).strip()
            ]
            self.status_var.set(
                f"Хост обновил важные факты ({len(self.important_facts)})."
            )

        elif mtype == "actions":

            self._render_buttons(msg.get("actions") or [])

        elif mtype == "players":
            names = msg.get("players") or []
            self.status_var.set(
                "Игроков в игре: " + (", ".join(names) if names else "—")
            )


        elif mtype == "reset":

            self._set_story_text("")

            self._story_buffer = ""

            self.card_store = CardStore()
            self.quest_store = QuestStore()
            self.location_store = LocationStore()
            self.current_location = ""
            self._render_buttons([])
            cfg_dict = msg.get("cfg") or {}
            try:
                self.cfg = from_dict(cfg_dict)
            except Exception:
                pass
            self._append_story(f"=== {self.cfg.title} ===")

        elif mtype == "player_state":
            state = msg.get("state") or {}
            try:
                self.player_state = PlayerState.from_dict(state)
            except Exception:
                pass


        elif mtype == "system":
            text = msg.get("text") or ""
            if text:
                self._append_story(f"*** {text} ***")
    def _handle_ai_reply(self, payload):
        # payload — dict с ключами text/usage/user_message,
        # но для совместимости принимаем и просто строку.
        if isinstance(payload, dict):
            reply = payload.get("text", "") or ""
            usage = payload.get("usage") or {}
            user_message = payload.get("user_message", "") or ""
        else:
            reply = payload or ""
            usage = {}
            user_message = ""

        self._is_processing = False
        self._stop_typing_animation()
        try:
            self.cancel_ai_btn.configure(state="disabled")
        except (AttributeError, tk.TclError):
            pass
        (narrative, actions, cards, quests,
         rolls, locations, plugin_data) = parse_ai_response(
            reply, plugin_tags=self.plugin_manager.get_tag_handlers()
        )

        self.history.append({"role": "assistant", "content": reply})
        self.turn_count += 1

        # --- Статистика ---
        self.stats.add_turn(user_message, reply, usage)
        self._update_stats_label()

        self._append_story(narrative)
        self._last_narrative = narrative

        # Автоозвучка — только если включена и текст непустой.
        if narrative and self.auto_speak.get() and self.voice.is_available():
            self.voice.say(narrative)

        # --- Карточки ---
        new_cards, updated_cards = [], []
        for c in cards:
            try:
                res, action = self.card_store.update_or_add(c)
            except Exception:
                continue
            if res is None:
                continue
            (new_cards if action == "added" else updated_cards).append(res)

        # --- Квесты ---
        new_quests, updated_quests = [], []
        for q in quests:
            try:
                res, action = self.quest_store.update_or_add(
                    q, turn_count=self.turn_count
                )
            except Exception:
                continue
            if res is None:
                continue
            (new_quests if action == "added" else updated_quests).append(res)

        # --- Локации ---
        new_locs, updated_locs = [], []
        location_changed = False
        for loc in locations:
            is_current = bool(loc.get("current"))
            try:
                res, action = self.location_store.update_or_add(
                    loc, discovered=True
                )
            except Exception:
                continue
            if res is None:
                continue
            (new_locs if action == "added" else updated_locs).append(res)
            if is_current and res["name"] != self.current_location:
                self.current_location = res["name"]
                location_changed = True

        # --- Статусная строка ---
        parts = []
        if new_cards or updated_cards:
            sub = []
            if new_cards:
                sub.append("новые: " + ", ".join(c["name"] for c in new_cards))
            if updated_cards:
                sub.append("обновлены: " +
                           ", ".join(c["name"] for c in updated_cards))
            parts.append("Карточки — " + "; ".join(sub))
        if new_quests or updated_quests:
            sub = []
            if new_quests:
                sub.append("новые: " + ", ".join(q["name"] for q in new_quests))
            if updated_quests:
                sub.append("обновлены: " +
                           ", ".join(q["name"] for q in updated_quests))
            parts.append("Квесты — " + "; ".join(sub))
        if new_locs or updated_locs:
            sub = []
            if new_locs:
                sub.append("новые: " + ", ".join(l["name"] for l in new_locs))
            if updated_locs:
                sub.append("обновлены: " +
                           ", ".join(l["name"] for l in updated_locs))
            parts.append("Карта — " + "; ".join(sub))
        if location_changed:
            parts.append(f"Локация героя: {self.current_location}")

        if parts:
            self.status_var.set(" | ".join(parts))
        else:
            key_label = self.ai.current_key_label()
            self.status_var.set(
                "Готово." + (f" ({key_label})" if key_label else "")
            )

        self._render_buttons(actions)

        # --- Рассылка клиентам (только хост) ---
        if self.mode == "host" and self.server:
            self.server.broadcast({"type": "narrative", "text": narrative})
            self.server.broadcast({
                "type": "player_state",
                "state": self.player_state.to_dict(),
            })
            if new_cards or updated_cards:
                self.server.broadcast({
                    "type": "cards",
                    "cards": new_cards + updated_cards,
                })
            if new_quests or updated_quests:
                self.server.broadcast({
                    "type": "quests",
                    "quests": new_quests + updated_quests,
                })
            if new_locs or updated_locs:
                self.server.broadcast({
                    "type": "locations",
                    "locations": new_locs + updated_locs,
                })
            if location_changed:
                self.server.broadcast({
                    "type": "current_location",
                    "name": self.current_location,
                })
            if actions:
                self.server.broadcast({"type": "actions", "actions": actions})

        # --- Плагинные хуки конца хода ---
        try:
            turn_ctx = self._build_plugin_context(plugin_data=plugin_data)
            for hook in self.plugin_manager.get_turn_end_hooks():
                try:
                    hook(turn_ctx)
                except Exception as e:
                    try:
                        self.app_logger.log_error(
                            "plugin", e, {"context": "turn_end_hook"}
                        )
                    except Exception:
                        pass
        except Exception:
            pass

        self._maybe_compress_history()

        # Разрешение бросков — если ИИ их запросил.
        if rolls:
            self._resolve_rolls(rolls)
        else:
            # Продолжение без броска разрывает цепочку авто-бросков.
            self._auto_roll_chain = 0

    # ---- Броски кубика --------------------------------------------------

    def _resolve_rolls(self, rolls: list):
        """
        Резолвит все запрошенные ИИ броски и отправляет результат обратно.
        На клиенте ничего не делает — броски всегда кидает хост.
        """
        if self.mode == "client":
            return

        eff = self.player_state.get_effective_stats()

        def _find_bonus(name: str) -> int:
            name_l = str(name).strip().lower()
            for k, v in eff.items():
                if str(k).strip().lower() == name_l:
                    return int(v)
            for k, v in eff.items():
                kl = str(k).strip().lower()
                if kl in name_l or name_l in kl:
                    return int(v)
            return 0

        story_lines = ["🎲 Броски:"]
        ai_lines = ["Результаты бросков (d20 + характеристика):"]

        for r in rolls:
            stat = r.get("stat", "?")
            dc = int(r.get("dc", 10))
            label = (r.get("label") or "").strip()
            bonus = _find_bonus(stat)
            d20 = random.randint(1, 20)
            total = d20 + bonus
            success = total >= dc

            verdict = "успех" if success else "провал"
            head = stat if not label else f"{label} ({stat})"
            bonus_str = f"+{bonus}" if bonus >= 0 else str(bonus)

            story_lines.append(
                f"   • {head}: d20={d20}, бонус {bonus_str}, "
                f"итого {total} против {dc} — {verdict}"
            )
            ai_lines.append(
                f"- {head}: {d20} + {bonus} = {total} против {dc} — {verdict}"
            )

        story_text = "\n".join(story_lines)
        self._append_story(story_text)
        self.status_var.set(story_lines[1] if len(story_lines) > 1
                            else "Броски выполнены.")

        if self.mode == "host" and self.server:
            self.server.broadcast({"type": "narrative", "text": story_text})

        # Защита от зацикливания.
        self._auto_roll_chain += 1
        if self._auto_roll_chain > AUTO_ROLL_CHAIN_LIMIT:
            self._append_story(
                "*** Слишком много последовательных проверок — "
                "жду вашего действия. ***"
            )
            self._auto_roll_chain = 0
            return

        user_msg = "\n".join(ai_lines)
        self.after(
            120,
            lambda m=user_msg: self._send_to_ai(
                user_message=m,
                multiplayer=(self.mode == "host"),
            ),
        )

    # ---- Сжатие истории -------------------------------------------------

    def _maybe_compress_history(self):
        if self._compressing:
            return
        if len(self.history) < HISTORY_COMPRESS_TRIGGER:
            return

        split_at = len(self.history) - HISTORY_KEEP_RECENT
        old_part = self.history[:split_at]
        if not old_part:
            return

        self._compressing = True
        previous_summary = self.story_summary

        def worker():
            try:
                new_summary = self.ai.summarize_dialogue(old_part, previous_summary)
                self.result_queue.put(("summary", (new_summary, split_at)))
            except Exception as e:
                self.result_queue.put(("summary_error", str(e)))

        threading.Thread(target=worker, daemon=True).start()

    def _handle_summary_result(self, payload):
        new_summary, split_at = payload
        self.story_summary = new_summary
        if len(self.history) >= split_at:
            self.history = self.history[split_at:]
        self._compressing = False
        self.status_var.set(
            "История сжата в краткую память сюжета — экономим токены."
        )

    def _set_story_text(self, text):
        self._story_buffer = text or ""
        self.story_text.configure(state="normal")
        self.story_text.delete("1.0", "end")
        if self._story_buffer:
            _insert_markdown(self.story_text, self._story_buffer)
        self.story_text.configure(state="disabled")
        self.story_text.see("end")

    def _append_story(self, text):
        if not text:
            return
        text = text.rstrip("\n")
        if self._story_buffer:
            self._story_buffer += "\n\n" + text
        else:
            self._story_buffer = text

        smart = bool(getattr(self.settings, "smart_scroll", True))
        was_at_bottom = self._is_story_at_bottom() if smart else True

        self.story_text.configure(state="normal")
        prefix = "" if self.story_text.index("end-1c") == "1.0" else "\n\n"
        if prefix:
            self.story_text.insert("end", prefix)
        _insert_markdown(self.story_text, text)
        self.story_text.configure(state="disabled")
        if was_at_bottom:
            self.story_text.see("end")

    def _on_close(self):
        # Автосейв перед закрытием — не должен мешать выходу ни при каких
        # обстоятельствах, поэтому обёрнут в широкий try/except.
        try:
            self._autosave()
        except Exception:
            pass

        # Останавливаем озвучку, чтобы поток не висел в runAndWait().
        try:
            self.voice.shutdown()
        except Exception:
            pass

        self._closing = True
        try:
            if self.server:
                self.server.stop()
                self.server = None
            if self.client_net:
                self.client_net.close()
                self.client_net = None
        except Exception:
            pass
        try:
            self.destroy()
        except Exception:
            pass


def main():
    app = MainApp()
    app.mainloop()


if __name__ == "__main__":
    main()