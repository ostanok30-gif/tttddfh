# -*- coding: utf-8 -*-
import re, time, random, datetime, sqlite3, threading, logging, os, requests, json, asyncio, zipfile, io, shutil, html as html_entities, itertools
import hmac, hashlib, urllib.parse, uuid
from concurrent.futures import ThreadPoolExecutor, as_completed, wait, FIRST_COMPLETED, TimeoutError as FuturesTimeoutError
from urllib3.util.retry import Retry
from telebot import types
import telebot

# python-dotenv подтягивает переменные из .env при локальном запуске.
# На bothost.ru (и вообще в любом Docker-хостинге) переменные окружения задаются
# через панель/dashboard, .env там не нужен — load_dotenv() в этом случае просто
# ничего не найдёт и молча пропустится (override=False по умолчанию).
try:
    from dotenv import load_dotenv
    load_dotenv()
except ImportError:
    pass
from telethon import TelegramClient, errors
from telethon.sessions import StringSession
from telethon.tl.functions.contacts import ResolveUsernameRequest
from telethon.tl.functions.account import CheckUsernameRequest
from telethon.tl.functions.payments import GetSavedStarGiftsRequest
from telethon.tl.types import InputPeerSelf, PeerUser
from requests.adapters import HTTPAdapter

MOSCOW_TZ = datetime.timezone(datetime.timedelta(hours=3))

def moscow_now():
    return datetime.datetime.now(MOSCOW_TZ)

def moscow_today_start():
    now = moscow_now()
    return now.replace(hour=0, minute=0, second=0, microsecond=0)

def get_ram_usage():
    try:
        with open('/proc/meminfo', 'r') as f: mem = f.read()
        total = int(re.search(r'MemTotal:\s+(\d+)', mem).group(1)) // 1024
        free = int(re.search(r'MemAvailable:\s+(\d+)', mem).group(1)) // 1024
        return f"{total - free}MB / {total}MB"
    except: return "N/A"

def get_cpu_usage():
    try:
        with open('/proc/stat', 'r') as f: cpu_line = f.readline()
        cpu_parts = cpu_line.split(); idle = int(cpu_parts[4]); total = sum(int(x) for x in cpu_parts[1:])
        return f"{100 - idle * 100 // total}%"
    except: return "N/A"

SESSION_DIR = 'sessions'
os.makedirs(SESSION_DIR, exist_ok=True)

logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

_async_loop = asyncio.new_event_loop()
def _start_async_loop(loop):
    asyncio.set_event_loop(loop)
    loop.run_forever()
threading.Thread(target=_start_async_loop, args=(_async_loop,), daemon=True).start()

def run_async(coro, timeout=20):
    async def _with_timeout():
        return await asyncio.wait_for(coro, timeout=timeout)
    try:
        # timeout+2 — небольшой запас, чтобы именно внутренний wait_for успел отменить
        # зависшую корутину на event loop'е раньше, чем мы перестанем ждать результат здесь
        return asyncio.run_coroutine_threadsafe(_with_timeout(), _async_loop).result(timeout=timeout + 2)
    except (FuturesTimeoutError, asyncio.TimeoutError):
        logger.warning(f"run_async: таймаут {timeout}с — корутина отменена на event loop'е")
        raise TimeoutError(f"run_async timed out after {timeout}s")

def _env(name, default=None, required=False):
    val = os.getenv(name, default)
    if required and not val:
        raise RuntimeError(
            f"Переменная окружения {name} не задана. Скопируйте .env.example в .env "
            f"(локально) или задайте {name} в панели переменных окружения хостинга."
        )
    return val

TOKEN = _env('BOT_TOKEN', required=True)
bot = telebot.TeleBot(TOKEN, num_threads=40)

# Отдельные боты только для проверки юзернеймов (getChat) — чтобы не сажать
# флуд-контроль основного бота и распределять нагрузку между несколькими токенами.
# Задаются одной строкой через запятую: CHECK_BOT_TOKENS=token1,token2,token3
CHECK_BOT_TOKENS = [t.strip() for t in _env('CHECK_BOT_TOKENS', '').split(',') if t.strip()]
_check_bots = [telebot.TeleBot(t, threaded=False) for t in CHECK_BOT_TOKENS]
_check_bot_idx_lock = threading.Lock()
_check_bot_idx = [0]
def _next_check_bot():
    if not _check_bots:
        # CHECK_BOT_TOKENS не задан — используем основного бота как запасной вариант.
        return bot
    with _check_bot_idx_lock:
        i = _check_bot_idx[0] % len(_check_bots)
        _check_bot_idx[0] += 1
    return _check_bots[i]

conn = sqlite3.connect('users.db', check_same_thread=False)
# По умолчанию SQLite на каждый commit() делает синхронный fsync на диск, а таких
# commit() в коде десятки — почти любое действие пользователя (get_user/update_user)
# идёт под одним общим db_lock. Под нагрузкой, особенно на "находке" (там подряд идёт
# 4-5 отдельных commit'ов: found_count, дневной лимит, INSERT INTO found,
# total_searches), каждый fsync блокирует АБСОЛЮТНО ВСЕХ остальных активных
# пользователей, ждущих своей очереди на этот же лок — отсюда "еле-еле пишет" при
# активном трафике и заметный лаг именно в момент находки ника.
# WAL-режим убирает необходимость fsync на каждый commit: изменения дописываются в
# отдельный журнal, чтения при этом вообще не блокируются записью. synchronous=NORMAL
# (безопасно совместно с WAL) не гарантирует данные при отключении питания в момент
# записи, но полностью исключает потерю/повреждение при обычном падении процесса —
# приемлемый компромисс для бота. busy_timeout — на случай короткой конкуренции за
# сам файл БД на уровне ОС.
conn.execute("PRAGMA journal_mode=WAL")
conn.execute("PRAGMA synchronous=NORMAL")
conn.execute("PRAGMA busy_timeout=5000")
cursor = conn.cursor()
db_lock = threading.RLock()

ADMIN_ID = int(_env('ADMIN_ID', required=True))
REQUIRED_CHANNEL = _env('REQUIRED_CHANNEL', '@vocmaq')
CHANNEL_LINK = _env('CHANNEL_LINK', 'https://t.me/vocmaq')
API_ID = int(_env('TG_API_ID', required=True))
API_HASH = _env('TG_API_HASH', required=True)

CRYPTO_BOT_TOKEN = _env('CRYPTO_BOT_TOKEN', required=True)
CRYPTO_BOT_API_URL = _env('CRYPTO_BOT_API_URL', 'https://pay.crypt.bot/api')
CRYPTO_DAY_PRICE_USD_DEFAULT = float(_env('CRYPTO_DAY_PRICE_USD_DEFAULT', '0.35'))

# URL мини-приложения (страница webapp/index.html, бывший v.html). Если задан —
# в главном меню появляется кнопка "Открыть приложение", открывающая её как
# Telegram WebApp. Должен быть https-адресом (см. README.md).
WEBAPP_URL = _env('WEBAPP_URL', '')

# --- Раздача webapp/index.html + JSON API тем же процессом, что и бот ---
# Нужна, только если у проекта на bothost.ru есть публичный порт/URL и хочется
# отдавать страницу и API без отдельного хостинга: SERVE_WEBAPP=1.
# Если страница уже захостена отдельно — просто укажи её https-адрес в
# WEBAPP_URL, этот блок тогда не запускается и не нужен.

# --- Проверка Telegram WebApp initData (см. https://core.telegram.org/bots/webapps#validating-data-received-via-the-mini-app) ---
INIT_DATA_MAX_AGE = 86400  # 24 часа — старее считаем протухшим (защита от replay)

def validate_init_data(init_data_str):
    """Проверяет подпись initData, присланного фронтом. Возвращает dict пользователя
    Telegram (как в initDataUnsafe.user) при успехе, либо None при любой ошибке
    (нет данных, битая подпись, протухший auth_date, некорректный JSON и т.п.).
    Именно отсюда, а не с фронта, всегда берётся user_id для всех /api/* операций."""
    if not init_data_str:
        return None
    try:
        pairs = urllib.parse.parse_qsl(init_data_str, strict_parsing=True, keep_blank_values=True)
    except ValueError:
        return None
    data = dict(pairs)
    received_hash = data.pop('hash', None)
    if not received_hash:
        return None
    data_check_string = '\n'.join(f"{k}={v}" for k, v in sorted(data.items()))
    secret_key = hmac.new(b"WebAppData", TOKEN.encode(), hashlib.sha256).digest()
    computed_hash = hmac.new(secret_key, data_check_string.encode(), hashlib.sha256).hexdigest()
    if not hmac.compare_digest(computed_hash, received_hash):
        return None
    try:
        auth_date = int(data.get('auth_date', '0'))
    except ValueError:
        return None
    if auth_date <= 0 or (time.time() - auth_date) > INIT_DATA_MAX_AGE:
        return None
    try:
        user = json.loads(data.get('user', '{}'))
    except (json.JSONDecodeError, TypeError):
        return None
    if not user or 'id' not in user:
        return None
    return user

# --- Фоновые задачи поиска, запущенные с сайта (мини-приложения) ---
# Flask-воркер не блокируется на время поиска: POST /api/search сразу запускает
# threading.Thread и возвращает task_id, а фронт опрашивает GET /api/search/<id>.
_webapp_tasks = {}
_webapp_tasks_lock = threading.Lock()
WEBAPP_TASK_TTL = 300  # 5 минут — старые задачи вычищаются

def _cleanup_webapp_tasks():
    now = time.time()
    with _webapp_tasks_lock:
        stale = [tid for tid, t in _webapp_tasks.items() if now - t['started_at'] > WEBAPP_TASK_TTL]
        for tid in stale:
            del _webapp_tasks[tid]

def _schedule_webapp_task_cleanup():
    while True:
        time.sleep(60)
        try: _cleanup_webapp_tasks()
        except Exception as e: logger.warning(f"_cleanup_webapp_tasks: {e}")

threading.Thread(target=_schedule_webapp_task_cleanup, daemon=True).start()

def _run_webapp_search(task_id, user_id, kind, params):
    cancel_ev = threading.Event()
    with _webapp_tasks_lock:
        _webapp_tasks[task_id]['cancel_event'] = cancel_ev
    ok, reason = try_start_check(user_id)
    if not ok:
        with _webapp_tasks_lock:
            _webapp_tasks[task_id]['status'] = 'error'
            _webapp_tasks[task_id]['message'] = 'already_running' if reason == 'already_running' else 'overload'
        return
    try:
        if kind == 'len':
            result = find_username(user_id, params['length'], params.get('mode', 'nodigits'), cancel_event=cancel_ev)
        elif kind == 'filter':
            result = find_by_filter(user_id, params.get('mask', ''), cancel_event=cancel_ev)
        elif kind == 'word':
            result = find_by_word(user_id, params.get('word', ''), params.get('word_type', 'random'), cancel_event=cancel_ev)
        else:
            result = {'status': 'error', 'message': 'unknown search type'}
    except Exception as e:
        logger.error(f"_run_webapp_search[{task_id}]: {e}")
        result = {'status': 'error', 'message': 'internal error'}
    finally:
        end_check(user_id)
    with _webapp_tasks_lock:
        if task_id in _webapp_tasks:
            _webapp_tasks[task_id]['status'] = result.get('status', 'error')
            _webapp_tasks[task_id]['result'] = result

def _start_webapp_server():
    try:
        from flask import Flask, send_from_directory, request, jsonify
    except ImportError:
        logger.warning("SERVE_WEBAPP=1, но пакет flask не установлен — раздача страницы пропущена")
        return
    webapp_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'webapp')
    app = Flask(__name__)

    def _init_data_from_get():
        return request.args.get('initData', '')

    def _init_data_from_body():
        body = request.get_json(silent=True) or {}
        return body.get('initData', ''), body

    def _require_user_get():
        user = validate_init_data(_init_data_from_get())
        if not user:
            return None, (jsonify({'error': 'unauthorized'}), 401)
        return user, None

    def _require_user_body():
        init_data, body = _init_data_from_body()
        user = validate_init_data(init_data)
        if not user:
            return None, None, (jsonify({'error': 'unauthorized'}), 401)
        return user, body, None

    @app.route('/')
    def _index():
        return send_from_directory(webapp_dir, 'index.html')

    @app.route('/api/profile', methods=['GET'])
    def api_profile():
        user, err = _require_user_get()
        if err: return err
        user_id = user['id']
        db_user = get_user(user_id)
        if not db_user:
            db_user, _ = create_user(user_id, username=user.get('username'))
        expires = db_user.get('premium_expires')
        return jsonify({
            'total_searches': db_user.get('total_searches', 0) or 0,
            'found_count': db_user.get('found_count', 0) or 0,
            'referrals_count': db_user.get('referrals_count', 0) or 0,
            'days_in_bot': _days_in_bot(db_user),
            'premium': has_premium(user_id),
            'premium_expires': expires,
            'free_searches_left': free_searches_left(user_id),
        })

    @app.route('/api/referral', methods=['GET'])
    def api_referral():
        user, err = _require_user_get()
        if err: return err
        user_id = user['id']
        db_user = get_user(user_id)
        if not db_user:
            db_user, _ = create_user(user_id, username=user.get('username'))
        refs = db_user.get('referrals_count', 0) or 0
        try:
            bot_username = bot.get_me().username
        except Exception:
            bot_username = None
        link = f"https://t.me/{bot_username}?start={user_id}" if bot_username else None
        return jsonify({
            'referrals_count': refs,
            'progress': refs % 5,
            'link': link,
        })

    @app.route('/api/traps', methods=['GET'])
    def api_traps_list():
        user, err = _require_user_get()
        if err: return err
        user_id = user['id']
        with db_lock:
            cursor.execute("SELECT target_username, status, created_date FROM traps WHERE user_id=? ORDER BY created_date DESC", (user_id,))
            rows = cursor.fetchall()
        return jsonify({'traps': [{'username': r[0], 'status': r[1], 'created_date': r[2]} for r in rows]})

    @app.route('/api/traps', methods=['POST'])
    def api_traps_set():
        user, body, err = _require_user_body()
        if err: return err
        user_id = user['id']
        target = (body.get('username') or '').strip().replace('@', '').lower()
        if not target or len(target) < 5 or not all(c in 'abcdefghijklmnopqrstuvwxyz0123456789_' for c in target):
            return jsonify({'error': 'invalid_username'}), 400
        with db_lock:
            cursor.execute("SELECT COUNT(*) FROM traps WHERE user_id=? AND status='active'", (user_id,))
            if cursor.fetchone()[0] >= 3:
                return jsonify({'error': 'too_many_traps'}), 400
            cursor.execute("SELECT 1 FROM traps WHERE user_id=? AND target_username=? AND status='active'", (user_id, target))
            if cursor.fetchone():
                return jsonify({'error': 'duplicate'}), 400
        if checker.check(target):
            return jsonify({'error': 'already_free', 'username': target}), 400
        now = moscow_now().strftime('%Y-%m-%d %H:%M:%S')
        with db_lock:
            cursor.execute("INSERT INTO traps (user_id, target_username, status, created_date) VALUES (?,?,'active',?)", (user_id, target, now))
            conn.commit()
        return jsonify({'ok': True, 'username': target})

    @app.route('/api/traps/<username>', methods=['DELETE'])
    def api_traps_delete(username):
        init_data = request.args.get('initData', '')
        user = validate_init_data(init_data)
        if not user:
            return jsonify({'error': 'unauthorized'}), 401
        user_id = user['id']
        target = username.strip().replace('@', '').lower()
        with db_lock:
            cursor.execute("DELETE FROM traps WHERE user_id=? AND target_username=?", (user_id, target))
            deleted = cursor.rowcount
            conn.commit()
        return jsonify({'ok': True, 'deleted': deleted})

    @app.route('/api/history', methods=['GET'])
    def api_history():
        user, err = _require_user_get()
        if err: return err
        user_id = user['id']
        with db_lock:
            cursor.execute("SELECT username, length, found_date FROM found WHERE finder_id=? ORDER BY found_date DESC LIMIT 50", (user_id,))
            rows = cursor.fetchall()
        return jsonify({'history': [{'username': r[0], 'length': r[1], 'found_date': r[2]} for r in rows]})

    @app.route('/api/search', methods=['POST'])
    def api_search_start():
        user, body, err = _require_user_body()
        if err: return err
        user_id = user['id']
        kind = body.get('type')
        if kind not in ('len', 'filter', 'word'):
            return jsonify({'error': 'invalid_type'}), 400
        params = {}
        if kind == 'len':
            length = body.get('length')
            if length not in (5, 6):
                return jsonify({'error': 'invalid_length'}), 400
            mode = body.get('mode', 'nodigits')
            if mode not in ('digits', 'nodigits'):
                return jsonify({'error': 'invalid_mode'}), 400
            params = {'length': length, 'mode': mode}
        elif kind == 'filter':
            params = {'mask': body.get('mask', '')}
        elif kind == 'word':
            word_type = body.get('word_type', 'random')
            if word_type not in ('prefix', 'suffix', 'random'):
                return jsonify({'error': 'invalid_word_type'}), 400
            params = {'word': body.get('word', ''), 'word_type': word_type}
        task_id = uuid.uuid4().hex
        with _webapp_tasks_lock:
            _webapp_tasks[task_id] = {'status': 'running', 'result': None, 'started_at': time.time(), 'cancel_event': None}
        threading.Thread(target=_run_webapp_search, args=(task_id, user_id, kind, params), daemon=True).start()
        return jsonify({'task_id': task_id})

    @app.route('/api/search/<task_id>', methods=['GET'])
    def api_search_status(task_id):
        # Тоже требует валидный initData, чтобы не дать подсмотреть чужую задачу.
        user, err = _require_user_get()
        if err: return err
        with _webapp_tasks_lock:
            task = _webapp_tasks.get(task_id)
        if not task:
            return jsonify({'status': 'error', 'message': 'not_found'}), 404
        status = task['status']
        if status == 'running':
            return jsonify({'status': 'running'})
        result = task.get('result') or {}
        rstatus = result.get('status', status)
        if rstatus == 'found':
            return jsonify({'status': 'found', 'username': result['username'], 'rating': result.get('rating')})
        if rstatus == 'not_found':
            return jsonify({'status': 'not_found'})
        if rstatus == 'cancelled':
            return jsonify({'status': 'cancelled'})
        if rstatus == 'cooldown':
            return jsonify({'status': 'error', 'message': f"cooldown:{result.get('seconds', 1)}"})
        if rstatus == 'no_search_left':
            return jsonify({'status': 'error', 'message': 'no_search_left'})
        return jsonify({'status': 'error', 'message': result.get('message') or status})

    @app.route('/api/search/<task_id>/cancel', methods=['POST'])
    def api_search_cancel(task_id):
        user, body, err = _require_user_body()
        if err: return err
        with _webapp_tasks_lock:
            task = _webapp_tasks.get(task_id)
            if task and task.get('cancel_event'):
                task['cancel_event'].set()
        return jsonify({'ok': True})

    @app.route('/<path:filename>')
    def _static(filename):
        return send_from_directory(webapp_dir, filename)

    port = int(_env('PORT', '8080'))
    threading.Thread(
        target=lambda: app.run(host='0.0.0.0', port=port, use_reloader=False),
        daemon=True,
    ).start()
    logger.info(f"Страница мини-приложения и API раздаются на 0.0.0.0:{port}")

if _env('SERVE_WEBAPP', 'false').strip().lower() in ('1', 'true', 'yes', 'on'):
    _start_webapp_server()

def _fetch_direct(target_url, headers=None, timeout=5, allow_redirects=True):
    """Прямой запрос без прокси."""
    return _http_session.get(target_url, headers=headers, timeout=timeout, allow_redirects=allow_redirects)



SEARCH_ATTEMPTS = 25
FILTER_ATTEMPTS = 60
# Кап на кол-во одновременно активных Telegram-аккаунтов в пуле сессий.
# Подняли с 5 — если в базе появится больше сохранённых сессий, пул сможет ими воспользоваться
# и параллельно обслуживать больше одновременных поисков (под 20+ человек одним ботом).
MAX_ACTIVE_SESSIONS = 10
CHECK_WORKERS = 15
# HTTP+fragment проверка (checker.check) дешёвая и не трогает Telegram-сессии — ею не лимитируем.
# А проверка через сессию (verify_with_session) дорогая и рискованная для аккаунтов,
# поэтому на неё отдельный бюджет на один поиск, не привязанный к SEARCH_ATTEMPTS/FILTER_ATTEMPTS.
# 12 оказалось слишком мало — HTTP-фильтр даёт много ложных "свободен", и поиск часто исчерпывал
# бюджет впустую до того, как попадался реально свободный ник. Подняли до 30: пул сессий теперь
# (MAX_ACTIVE_SESSIONS=10, MIN_DELAY=5с) тянет это без проблем даже под нагрузкой.
SESSION_VERIFY_LIMIT = 30
# Было 2с — при 10+ одновременных поисках (десятки параллельных HTTP-запросов на
# t.me/fragment.com сразу) 2с стабильно не хватало и запросы валились в 'error',
# который раньше засчитывался как "занято". Теперь 'error' уже не значит "занято"
# (см. UsernameChecker.check), но и сам таймаут лучше сделать реалистичным.
REQUEST_TIMEOUT = 3
MAINTENANCE_MODE = _env('MAINTENANCE_MODE', 'false').strip().lower() in ('1', 'true', 'yes', 'on')
FREE_DAILY_SEARCHES = 5
user_last_action = {}

prefixes = []; suffixes = []
for c in 'abcdefghijklmnopqrstuvwxyz': prefixes.append(c); suffixes.append(c)
for c1 in 'abcdefghijklmnopqrstuvwxyz':
    for c2 in 'abcdefghijklmnopqrstuvwxyz': prefixes.append(c1 + c2); suffixes.append(c1 + c2)

popular_prefixes = ['my','mr','ms','dr','dj','mc','la','le','da','de','do','el','ka','ki','ko','ma','mi','mo','the','real','just','best','super','pro','top','ultra','mega','hyper','cyber','tech','nexus','alpha','beta','gamma','delta','omega','sigma','prime','elite','crypto','neo','pixel','byte','dark','light','fire','ice','wind','earth','water','sky','star','moon','sun','void','zero','ghost','shadow','storm','frost','flux','apex','zen','raw','wild','pure','holy','evil','mad','crazy','lazy','happy','angry','lil','big','fat','slim','metal','iron','steel','gold','silver','bronze','crystal','ruby','jade','opal','onyx','pearl','blood','bone','skull','soul','mind','brain','head','face','eye','hand','foot','claw','fang','blade','axe','sword','gun','laser','rocket','drone','mech','robo','digi','techno','go','get','fly','run','jump','kick','punch','hit','strike','slash','shoot','blast','burn','freeze','hack','crack','lock','load','play','spin','twist','turn','roll','drop','dash','rush','crash','smash','make','take','give','send','link','ping','call','seek','find','lost','found','catch','watch','look','omni','infinity','eternal','chaos','order','logic','magic','myth','legend','fable','saga','epic','cosmic','astro','lunar','solar','polar','boreal','aurora','nebula','quasar','pulsar','comet','meteor','phoenix','dragon','tiger','wolf','hawk','eagle','viper','cobra','jaguar','panda','raven','crow','ninja','samurai','ronin','warrior','knight','archer','mage','wizard','witch','druid','monk','agent','pilot','captain','admiral','general','major','colonel','sarge','trooper','scout','ranger','commando','von','van','bin','al','ibn','san','sen','jr','sr','king','lord','sir','dame','lady','duke','master','grand','mini','micro','nano','quantum','turbo','rapid','swift','quick','silent','stealth']
popular_suffixes = ['er','or','ar','ir','ur','ix','ox','ax','ex','ux','iz','oz','az','ez','uz','tv','cc','gg','ss','zz','xx','yy','io','ai','co','me','sh','ly','app','dev','xyz','tech','ok','up','on','in','it','is','us','uk','go','hi','yo','ow','eh','ah','oh','uh','um','hm','sh','ps','hub','lab','box','max','pad','pod','bit','byte','chip','bot','net','link','sync','cast','ster','ify','core','ware','mind','base','port','soft','gram','code','data','nova','wave','volt','pulse','node','grid','ic','id','if','ik','il','im','in','ip','is','it','on','an','un','en','yn','us','um','zy','xy','xo','za','ze','zi','zo','zu','ist','ism','ity','ize','ise','ite','ive','ius','ium','ion','tion','sion','ness','less','ful','ous','ious','able','ible','ance','ence','ment','hood','ship','dom','bot','top','pop','hop','cop','map','cap','tap','lap','nap','man','fan','pan','van','tan','ran','can','ban','dan','gan','son','ton','mon','ron','kon','zon','yon','won','lon','hon','max','tax','fax','lax','wax','pax','rax','sax','yax','zax','pro','bro','cro','dro','gro','tro','wro','zro','kro','star','king','lord','fire','ice','dark','light','storm','thunder','shadow','online','store','blog','site','web','net','org','com','club','space','world','life','boom','bang','buzz','click','snap','pop','zip','zap','zoom','blip','beep','ping','pong','ding','dong']
for p in popular_prefixes:
    if p not in prefixes: prefixes.append(p)
for s in popular_suffixes:
    if s not in suffixes: suffixes.append(s)

E_HI='6035084557378654059'; E_WELCOME='5983580310292402968'; E_WHAT='6043960760130868895'
E_INFO_LIST='5886676966102274844'; E_MAIN='6042098561095570207'; E_WARN='5774022692642492953'
E_PLANE='6037397706505195857'; E_CHOOSE_WAY='6044117517847236354'; E_CHOOSE='5812150667812280629'
E_FOUND_NICK='6032850693348399258'; E_NICK_LABEL='5904630315946611415'; E_CLICKABLE='5778208881301787450'
E_LETTERS='5942923471263636603'; E_RATING='6032949275732742941'; E_CHANNEL_LABEL='6024008227564296298'
E_REF_TOP='6032949275732742941'; E_REF_LINK='5938525265838739643'; E_REF_SHARE='5771880672192893347'
E_REF_COUNT='6021618194228187816'; E_PROFILE='6024039683904772353'; E_ID_LABEL='6021625933759257863'
E_USERNAME_LABEL='6021683104068933429'; E_STATS_TITLE='6023933602507528561'
E_SEARCHES_LABEL='6021741116192201252'; E_FOUND_LABEL='6021738534916854774'
E_REFS_LABEL='6021366530619479608'; E_DAYS_IN_BOT='6019328362479097179'; E_FIRST_LOGIN='6021524310538065865'
E_REG_LABEL='6021524310538065865'
E_ACCESS_DENIED='6037249452824072506'; E_ACCESS_CHANNEL='5942734685976138521'
E_ADMIN_MENU='5775870512127283512'; E_ADMIN_BOT_MODE='5776424837786374634'; E_ADMIN_RAM='5904258298764334001'
E_ADMIN_CHOOSE='5895534923833413814'; E_ADMIN_REPORT='6030466823290360017'
E_ADMIN_NEW_USERS='6035084557378654059'; E_ADMIN_NEW_REF='6032609071373226027'
E_ADMIN_FOUND_NICKS='6043960760130868895'; E_ADMIN_REJECTED='6044118213631938928'
E_SESSIONS_TITLE='5778593237925105705'; E_SESSIONS_ACTIVE='5778299625370817409'
E_SESSIONS_CHECKS='5764638872000533034'
E_STATS_TOTAL='6032594876506312598'
E_STATS_BANNED='6037254263187443802'; E_STATS_SEARCHES='5888620056551625531'
E_STATS_FOUND='6041919344995209164'; E_STATS_ACTIVE_SESS='5938252440926163756'
E_STATS_WAITING='5891211339170326418'; E_STATS_FLOOD='6021789086681930128'
E_STATS_INVALID='5774077015388852135'; E_STATS_TOTAL_SESS='6019266192827489185'
E_STATS_CHECKS='5936143551854285132'; E_STATS_ACCURACY='6025879072368761539'
E_SESSION_LIST='6028205772117118673'; E_SESSION_ACTIVE='5920515922505765329'
E_SESSION_WAITING='5922272602784534896'; E_SESSION_FLOOD='5879995903955179148'
E_SESSION_STATUS='5773626993010546707'; E_SESSION_ADD='5850309953293653168'
E_SESSION_ADD_DESC='6039398100408209720'; E_SESSION_DELETE='6032636795387121097'
E_SESSION_DELETE_CHOOSE='5774022692642492953'; E_BROADCAST='6021418126061605425'
E_BROADCAST_DESC='6032636795387121097'; E_BROADCAST_CHOOSE='6030537007350944596'
E_TOP_REF='6021644067111180663'; E_TOP_REF_PLACE='6030425896546996257'
E_TECH_WORKS='5776428312414917091'; E_TECH_WORKS_TITLE='6030537810509828330'
E_BANNED='6041933986538721961'; E_BANNED_REASON='6030425896546996257'
E_HISTORY='6034847960515219908'; E_HISTORY_DESC='6032608126480421344'; E_HISTORY_NICK='6043896193887506430'
E_TRAP_TITLE='6028435952299413210'; E_TRAP_INFO='6030848053177486888'; E_TRAP_INPUT='6039729023343400390'
E_TRAP_ALERT='6030563507299160824'; E_TRAP_FREE='6037268453759389862'; E_TRAP_WARN='5843679481566335204'
E_TRAP_SET='5778570255555105942'; E_TRAP_NOTIFY='6050842281286570825'; E_TRAP_EXPIRE='5927118708873892465'
E_SETTINGS='5904258298764334001'; E_SETTINGS_MODE='5942734685976138521'
E_SETTINGS_READABLE='6041923781696426657'; E_SETTINGS_HINT='6030425896546996257'
E_MENU='5776424837786374634'
E_PREMIUM='6037533152593842454'

# --- Премиум-эмодзи для раздела "Промокод" ---
E_PROMO_STAR='5956561749070057536'; E_PROMO_PANEL='5875033614705495771'
E_PROMO_SEARCH='5874960879434338403'; E_PROMO_PIC='5888799736508454231'
E_PROMO_GEAR='5877260593903177342'; E_PROMO_GIFT='5875180111744995604'
E_PROMO_GIFT2='6032937473162614352'; E_PROMO_BACK='5877629862306385808'
E_PROMO_STAR2='5874948844935974490'; E_PROMO_TAG='5843862283964390528'
E_PROMO_OK='5825794181183836432'

# --- Премиум-эмодзи и цвет на кнопках (Bot API 9.4: icon_custom_emoji_id + style) ---
# pyTelegramBotAPI на момент написания не во всех версиях сериализует эти поля
# у InlineKeyboardButton/KeyboardButton "из коробки" (в конструкторе их может не
# быть в сигнатуре, а лишние **kwargs при to_dict() иногда просто отбрасываются).
# Чтобы не зависеть от версии библиотеки, ниже — тонкие обёртки, которые сами
# кладут icon_custom_emoji_id/style в итоговый dict перед отправкой в Telegram.
class PremiumInlineButton(types.InlineKeyboardButton):
    def __init__(self, text, emoji=None, style=None, **kwargs):
        super().__init__(text, **kwargs)
        self.icon_custom_emoji_id = emoji
        self.style = style

    def to_dict(self):
        d = super().to_dict()
        if self.icon_custom_emoji_id:
            d['icon_custom_emoji_id'] = self.icon_custom_emoji_id
        if self.style:
            d['style'] = self.style
        return d

    # часть версий pyTelegramBotAPI ещё используют старое имя метода
    def to_dic(self):
        return self.to_dict()

class PremiumKeyboardButton(types.KeyboardButton):
    def __init__(self, text, emoji=None, style=None, **kwargs):
        super().__init__(text, **kwargs)
        self.icon_custom_emoji_id = emoji
        self.style = style

    def to_dict(self):
        d = super().to_dict()
        if self.icon_custom_emoji_id:
            d['icon_custom_emoji_id'] = self.icon_custom_emoji_id
        if self.style:
            d['style'] = self.style
        return d

    def to_dic(self):
        return self.to_dict()

def btn(text, emoji=None, style=None, **kwargs):
    """Инлайн-кнопка с прем-эмодзи (icon_custom_emoji_id) и цветом (style:
    primary/success/danger). Требует Bot API 9.4+ и, для эмодзи, чтобы владелец
    бота либо купил доп. юзернейм на Fragment, либо имел Telegram Premium."""
    return PremiumInlineButton(text, emoji=emoji, style=style, **kwargs)

def kbtn(text, emoji=None, style=None, **kwargs):
    """Кнопка обычной (reply) клавиатуры с прем-эмодзи и цветом."""
    return PremiumKeyboardButton(text, emoji=emoji, style=style, **kwargs)

cursor.execute('''CREATE TABLE IF NOT EXISTS users (user_id INTEGER PRIMARY KEY, username TEXT, referrer_id INTEGER, referrals_count INTEGER DEFAULT 0, created_date TEXT, last_search_date TEXT, total_searches INTEGER DEFAULT 0, found_count INTEGER DEFAULT 0, rejected_count INTEGER DEFAULT 0, subscribed INTEGER DEFAULT 0, referral_activated INTEGER DEFAULT 0, banned INTEGER DEFAULT 0, search_mode TEXT DEFAULT 'random', is_premium INTEGER DEFAULT 0, premium_expires TEXT, daily_searches INTEGER DEFAULT 0, last_search_reset TEXT)''')
cursor.execute('''CREATE TABLE IF NOT EXISTS found (id INTEGER PRIMARY KEY AUTOINCREMENT, username TEXT UNIQUE, length INTEGER, price TEXT, found_date TEXT, finder_id INTEGER)''')
cursor.execute('''CREATE TABLE IF NOT EXISTS sessions (id INTEGER PRIMARY KEY AUTOINCREMENT, phone TEXT UNIQUE, session_string TEXT, status TEXT DEFAULT 'active', last_error TEXT, flood_until TEXT, created_at TEXT, updated_at TEXT, error_count INTEGER DEFAULT 0, last_used TEXT)''')
cursor.execute('''CREATE TABLE IF NOT EXISTS daily_stats (id INTEGER PRIMARY KEY AUTOINCREMENT, date TEXT UNIQUE, new_users INTEGER DEFAULT 0, new_refs INTEGER DEFAULT 0, found_nicks INTEGER DEFAULT 0, rejected_nicks INTEGER DEFAULT 0)''')
cursor.execute('''CREATE TABLE IF NOT EXISTS top_ref_excluded (username TEXT PRIMARY KEY)''')
cursor.execute('''CREATE TABLE IF NOT EXISTS traps (id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER, target_username TEXT, status TEXT DEFAULT 'active', created_date TEXT)''')
cursor.execute('''CREATE TABLE IF NOT EXISTS bot_settings (key TEXT PRIMARY KEY, value TEXT)''')
cursor.execute('''CREATE TABLE IF NOT EXISTS priemka_transactions (tx_id TEXT PRIMARY KEY, sender_id INTEGER, stars INTEGER, days INTEGER, status TEXT, created_at TEXT)''')
cursor.execute('''CREATE TABLE IF NOT EXISTS crypto_invoices (invoice_id TEXT PRIMARY KEY, user_id INTEGER, days INTEGER, amount_usd REAL, status TEXT, pay_url TEXT, created_at TEXT)''')
cursor.execute('''CREATE TABLE IF NOT EXISTS promocodes (code TEXT PRIMARY KEY, days INTEGER, max_activations INTEGER, activations_count INTEGER DEFAULT 0, created_by INTEGER, created_at TEXT, active INTEGER DEFAULT 1)''')
cursor.execute('''CREATE TABLE IF NOT EXISTS promo_activations (id INTEGER PRIMARY KEY AUTOINCREMENT, code TEXT, user_id INTEGER, activated_at TEXT, UNIQUE(code, user_id))''')
# Пул "лишних" ников: во время одного поиска параллельно проверяется несколько
# кандидатов через разные сессии (см. run_candidate_search); пользователю уходит
# только первый подтверждённый free, а остальные, которые тоже оказались free,
# раньше просто терялись — сессия уже потрачена на их проверку впустую. Теперь
# такие "лишние" ники складываются сюда и выдаются будущим поискам БЕЗ повторной
# проверки через сессии.
cursor.execute('''CREATE TABLE IF NOT EXISTS username_stock (id INTEGER PRIMARY KEY AUTOINCREMENT, username TEXT UNIQUE, length INTEGER, mode TEXT, created_at TEXT)''')
conn.commit()

# Миграция: если таблицы promocodes/promo_activations остались от более старой версии
# схемы (например, файл базы уже существовал до появления этой фичи), CREATE TABLE IF
# NOT EXISTS их не тронет — дорастим недостающие колонки вручную.
def _migrate_promo_tables():
    with db_lock:
        cursor.execute("PRAGMA table_info(promocodes)")
        cols = {row[1] for row in cursor.fetchall()}
        needed = {
            'days': 'INTEGER',
            'max_activations': 'INTEGER',
            'activations_count': 'INTEGER DEFAULT 0',
            'created_by': 'INTEGER',
            'created_at': 'TEXT',
            'active': 'INTEGER DEFAULT 1',
        }
        for col, coltype in needed.items():
            if col not in cols:
                cursor.execute(f"ALTER TABLE promocodes ADD COLUMN {col} {coltype}")

        cursor.execute("PRAGMA table_info(promo_activations)")
        cols2 = {row[1] for row in cursor.fetchall()}
        needed2 = {'code': 'TEXT', 'user_id': 'INTEGER', 'activated_at': 'TEXT'}
        for col, coltype in needed2.items():
            if col not in cols2:
                cursor.execute(f"ALTER TABLE promo_activations ADD COLUMN {col} {coltype}")
        conn.commit()
_migrate_promo_tables()

try: cursor.execute("ALTER TABLE users ADD COLUMN last_search_date TEXT"); conn.commit()
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN rejected_count INTEGER DEFAULT 0"); conn.commit()
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN search_mode TEXT DEFAULT 'random'"); conn.commit()
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN is_premium INTEGER DEFAULT 0"); conn.commit()
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN premium_expires TEXT"); conn.commit()
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN daily_searches INTEGER DEFAULT 0"); conn.commit()
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN last_search_reset TEXT"); conn.commit()
except: pass
try: cursor.execute("ALTER TABLE users ADD COLUMN premium_source TEXT"); conn.commit()
except: pass

def load_bot_settings():
    global SESSION_SEARCH_ENABLED
    with db_lock:
        cursor.execute("SELECT value FROM bot_settings WHERE key='session_search_enabled'")
        row = cursor.fetchone()
        if row:
            SESSION_SEARCH_ENABLED = row[0] == '1'
        else:
            SESSION_SEARCH_ENABLED = True
            cursor.execute("INSERT OR REPLACE INTO bot_settings (key, value) VALUES ('session_search_enabled', '1')")
            conn.commit()

def save_setting(key, value):
    with db_lock:
        cursor.execute("INSERT OR REPLACE INTO bot_settings (key, value) VALUES (?, ?)", (key, str(value)))
        conn.commit()

def get_setting(key, default=None):
    with db_lock:
        cursor.execute("SELECT value FROM bot_settings WHERE key=?", (key,))
        row = cursor.fetchone()
        return row[0] if row else default

SESSION_SEARCH_ENABLED = True
load_bot_settings()

# ==================== ПРИЁМКА ЗВЁЗД (авто-выдача премиума) ====================
PRIEMKA_SESSION = None
PRIEMKA_USERNAME = None
PRIEMKA_STARS_PER_DAY = 25
PRIEMKA_ENABLED = False

def load_priemka_settings():
    global PRIEMKA_SESSION, PRIEMKA_USERNAME, PRIEMKA_STARS_PER_DAY, PRIEMKA_ENABLED
    PRIEMKA_SESSION = get_setting('priemka_session') or None
    PRIEMKA_USERNAME = get_setting('priemka_username') or None
    try: PRIEMKA_STARS_PER_DAY = int(get_setting('priemka_stars_per_day', '25'))
    except: PRIEMKA_STARS_PER_DAY = 25
    PRIEMKA_ENABLED = get_setting('priemka_enabled', '0') == '1'

load_priemka_settings()

_priemka_client = None

async def _priemka_get_client():
    global _priemka_client
    if not PRIEMKA_SESSION:
        return None
    if _priemka_client is None:
        _priemka_client = TelegramClient(StringSession(PRIEMKA_SESSION), API_ID, API_HASH, loop=_async_loop)
    if not _priemka_client.is_connected():
        await _priemka_client.connect()
    return _priemka_client

async def _priemka_reset_client():
    global _priemka_client
    try:
        if _priemka_client and _priemka_client.is_connected():
            await _priemka_client.disconnect()
    except Exception:
        pass
    _priemka_client = None

async def _priemka_test_session(session_string):
    """Проверяет валидность session string и возвращает (ok, username_или_ошибка)."""
    client = TelegramClient(StringSession(session_string), API_ID, API_HASH, loop=_async_loop)
    try:
        await client.connect()
        if not await client.is_user_authorized():
            return False, "сессия не авторизована"
        me = await client.get_me()
        return True, (me.username or f"id{me.id}")
    except Exception as e:
        return False, str(e)
    finally:
        try: await client.disconnect()
        except Exception: pass

async def _priemka_fetch_gifts(limit=50):
    """Получает список подарков (звёздных гифтов), лежащих на аккаунте-приёмке.
    Важно: уже сконвертированные (обменянные на звёзды) подарки сюда не попадают —
    Telegram убирает их из списка сохранённых подарков сразу после конвертации."""
    client = await _priemka_get_client()
    if not client:
        return []
    if not await client.is_user_authorized():
        return []
    result = await client(GetSavedStarGiftsRequest(
        peer=InputPeerSelf(), offset='', limit=limit
    ))
    return result.gifts

def _priemka_gift_key(g):
    """Уникальный ключ подарка — чтобы не зачислить один и тот же подарок дважды."""
    saved_id = getattr(g, 'saved_id', None)
    msg_id = getattr(g, 'msg_id', None)
    date = getattr(g, 'date', None)
    date_str = date.isoformat() if hasattr(date, 'isoformat') else str(date)
    gift_id = getattr(getattr(g, 'gift', None), 'id', None)
    return f"gift:{saved_id or msg_id or 'x'}:{gift_id}:{date_str}"

def _mark_priemka_tx(tx_id, sender_id, stars, days, status):
    with db_lock:
        cursor.execute("INSERT OR REPLACE INTO priemka_transactions (tx_id, sender_id, stars, days, status, created_at) VALUES (?,?,?,?,?,?)",
                        (tx_id, sender_id, stars, days, status, moscow_now().strftime('%Y-%m-%d %H:%M:%S')))
        conn.commit()

def process_priemka_transactions():
    """Опрашивает аккаунт-приёмку по списку ПОДАРКОВ (не по общей истории транзакций,
    чтобы не путать реальные подарки от юзеров с внутренними событиями конвертации).
    Зачисляет премиум по Telegram ID реального отправителя подарка (без проверки юзернейма)."""
    if not PRIEMKA_ENABLED or not PRIEMKA_SESSION:
        return
    try:
        gifts = run_async(_priemka_fetch_gifts(50), timeout=25)
    except Exception as e:
        logger.error(f"Приёмка: ошибка получения подарков: {e}")
        return
    if not gifts:
        return
    for g in gifts:
        if getattr(g, 'refunded', False):
            continue
        tx_id = _priemka_gift_key(g)
        with db_lock:
            cursor.execute("SELECT 1 FROM priemka_transactions WHERE tx_id=?", (tx_id,))
            already = cursor.fetchone()
        if already:
            continue
        sender_id = None
        from_id = getattr(g, 'from_id', None)
        if isinstance(from_id, PeerUser):
            sender_id = from_id.user_id
        try:
            stars = int(getattr(getattr(g, 'gift', None), 'stars', 0) or 0)
        except Exception:
            stars = 0
        if not sender_id or stars <= 0:
            # подарок анонимный (скрыто имя отправителя) либо не удалось определить цену — нужна ручная выдача
            _mark_priemka_tx(tx_id, sender_id, stars, 0, 'unmatched')
            try:
                bot.send_message(ADMIN_ID, f"<tg-emoji emoji-id='{E_WARN}'>⚠️</tg-emoji> Приёмка: получен подарок на {stars}<tg-emoji emoji-id='{E_PREMIUM}'>⭐</tg-emoji>, но отправитель скрыт/анонимен. Начислите вручную при необходимости.", parse_mode='HTML')
            except: pass
            continue
        days = stars // max(PRIEMKA_STARS_PER_DAY, 1)
        if days <= 0:
            _mark_priemka_tx(tx_id, sender_id, stars, 0, 'too_small')
            try:
                bot.send_message(sender_id, f"<b><tg-emoji emoji-id='{E_WARN}'>⚠️</tg-emoji> Получен подарок на {stars} ⭐, но для 1 дня премиума нужно минимум {PRIEMKA_STARS_PER_DAY} ⭐. Отправьте ещё, и премиум зачислится автоматически.</b>", parse_mode='HTML')
            except: pass
            continue
        user = get_user(sender_id)
        if not user:
            _mark_priemka_tx(tx_id, sender_id, stars, days, 'no_user')
            try:
                bot.send_message(ADMIN_ID, f"<tg-emoji emoji-id='{E_WARN}'>⚠️</tg-emoji> Приёмка: получен подарок на {stars}<tg-emoji emoji-id='{E_PREMIUM}'>⭐</tg-emoji> от ID {sender_id}, который не запускал бота. Начислите вручную при необходимости через админ-панель (Премиум → По ID).", parse_mode='HTML')
            except: pass
            continue
        new_expires = grant_premium_days(sender_id, days)
        _mark_priemka_tx(tx_id, sender_id, stars, days, 'credited')
        try:
            bot.send_message(sender_id, f"<b><tg-emoji emoji-id='{E_PREMIUM}'>⭐</tg-emoji> Оплата получена: {stars}⭐</b>\n\n<blockquote><b>Премиум выдан на {days} дн.</b>\n<b>Истекает: {new_expires.strftime('%d.%m.%Y %H:%M')}</b></blockquote>", parse_mode='HTML')
        except: pass
        try:
            bot.send_message(ADMIN_ID, f"💰 Приёмка: начислено {days} дн. премиума пользователю {sender_id} за {stars}<tg-emoji emoji-id='{E_PREMIUM}'>⭐</tg-emoji>", parse_mode='HTML')
        except: pass

def schedule_priemka_check():
    while True:
        time.sleep(20)
        try:
            if PRIEMKA_ENABLED and PRIEMKA_SESSION:
                process_priemka_transactions()
        except Exception as e:
            logger.error(f"Приёмка: ошибка цикла проверки: {e}")

threading.Thread(target=schedule_priemka_check, daemon=True).start()

# ==================== ОПЛАТА КРИПТОВАЛЮТОЙ (CryptoBot / Crypto Pay API) ====================
def get_crypto_day_price():
    try: return float(get_setting('crypto_day_price_usd', str(CRYPTO_DAY_PRICE_USD_DEFAULT)))
    except: return CRYPTO_DAY_PRICE_USD_DEFAULT

def create_crypto_invoice(user_id, days):
    """Создаёт инвойс в CryptoBot на оплату премиума. Возвращает (pay_url, invoice_id) или (None, ошибка)."""
    price = get_crypto_day_price()
    amount = round(days * price, 2)
    if amount <= 0: amount = price
    headers = {'Crypto-Pay-API-Token': CRYPTO_BOT_TOKEN}
    payload = {
        'asset': 'USDT',
        'amount': str(amount),
        'description': f'Премиум на {days} дн.',
        'payload': f'{user_id}:{days}',
        'expires_in': 1800
    }
    try:
        resp = requests.post(f'{CRYPTO_BOT_API_URL}/createInvoice', headers=headers, json=payload, timeout=15)
        data = resp.json()
        if not data.get('ok'):
            return None, str(data.get('error') or data)
        result = data['result']
        pay_url = result.get('bot_invoice_url') or result.get('pay_url') or result.get('mini_app_invoice_url')
        invoice_id = str(result.get('invoice_id'))
        with db_lock:
            cursor.execute("INSERT OR REPLACE INTO crypto_invoices (invoice_id, user_id, days, amount_usd, status, pay_url, created_at) VALUES (?,?,?,?,?,?,?)",
                            (invoice_id, user_id, days, amount, 'active', pay_url, moscow_now().strftime('%Y-%m-%d %H:%M:%S')))
            conn.commit()
        return pay_url, invoice_id
    except Exception as e:
        return None, str(e)

def check_crypto_invoices():
    with db_lock:
        cursor.execute("SELECT invoice_id FROM crypto_invoices WHERE status='active'")
        pending_ids = [row[0] for row in cursor.fetchall()]
    if not pending_ids:
        return
    headers = {'Crypto-Pay-API-Token': CRYPTO_BOT_TOKEN}
    try:
        resp = requests.get(f'{CRYPTO_BOT_API_URL}/getInvoices', headers=headers,
                             params={'invoice_ids': ','.join(pending_ids)}, timeout=15)
        data = resp.json()
        if not data.get('ok'):
            logger.error(f"CryptoBot getInvoices error: {data}")
            return
        items = data['result'].get('items', [])
    except Exception as e:
        logger.error(f"CryptoBot getInvoices exception: {e}")
        return
    for inv in items:
        invoice_id = str(inv.get('invoice_id'))
        status = inv.get('status')
        if status not in ('paid', 'expired'):
            continue
        with db_lock:
            cursor.execute("SELECT user_id, days FROM crypto_invoices WHERE invoice_id=?", (invoice_id,))
            row = cursor.fetchone()
        if not row:
            continue
        user_id, days = row
        if status == 'expired':
            with db_lock:
                cursor.execute("UPDATE crypto_invoices SET status='expired' WHERE invoice_id=?", (invoice_id,))
                conn.commit()
            continue
        new_expires = grant_premium_days(user_id, days)
        with db_lock:
            cursor.execute("UPDATE crypto_invoices SET status='paid' WHERE invoice_id=?", (invoice_id,))
            conn.commit()
        if new_expires:
            try:
                bot.send_message(user_id, f"<b><tg-emoji emoji-id='{E_PREMIUM}'>⭐</tg-emoji> Оплата получена!</b>\n\n<blockquote><b>Премиум выдан на {days} дн.</b>\n<b>Истекает: {new_expires.strftime('%d.%m.%Y %H:%M')}</b></blockquote>", parse_mode='HTML')
            except: pass
        try:
            bot.send_message(ADMIN_ID, f"💳 CryptoBot: оплачен инвойс {invoice_id}, начислено {days} дн. пользователю {user_id}")
        except: pass

def schedule_crypto_check():
    while True:
        time.sleep(20)
        try: check_crypto_invoices()
        except Exception as e: logger.error(f"Крипто-оплата: ошибка цикла проверки: {e}")

threading.Thread(target=schedule_crypto_check, daemon=True).start()

def get_user_search_mode(user_id):
    user = get_user(user_id)
    if user and user.get('search_mode'):
        return user['search_mode']
    return 'random'

def set_user_search_mode(user_id, mode):
    with db_lock:
        cursor.execute("UPDATE users SET search_mode=? WHERE user_id=?", (mode, user_id))
        conn.commit()

def reset_daily_stats_if_new_day():
    today = moscow_now().strftime('%Y-%m-%d')
    with db_lock:
        cursor.execute("SELECT id FROM daily_stats WHERE date = ?", (today,))
        if not cursor.fetchone():
            yesterday = (moscow_now() - datetime.timedelta(days=1)).strftime('%Y-%m-%d')
            cursor.execute("SELECT COUNT(*) FROM users WHERE date(created_date) = ?", (yesterday,)); nu = cursor.fetchone()[0]
            cursor.execute("SELECT COUNT(*) FROM users WHERE date(created_date) = ? AND referral_activated = 1", (yesterday,)); nr = cursor.fetchone()[0]
            cursor.execute("SELECT COUNT(*) FROM found WHERE date(found_date) = ?", (yesterday,)); fy = cursor.fetchone()[0]
            cursor.execute("SELECT SUM(rejected_count) FROM users"); rt = cursor.fetchone()[0] or 0
            cursor.execute("INSERT OR REPLACE INTO daily_stats (date, new_users, new_refs, found_nicks, rejected_nicks) VALUES (?,?,?,?,?)", (yesterday, nu, nr, fy, rt))
            cursor.execute("UPDATE users SET rejected_count = 0")
            cursor.execute("INSERT OR IGNORE INTO daily_stats (date, new_users, new_refs, found_nicks, rejected_nicks) VALUES (?,0,0,0,0)", (today,))
            conn.commit()
reset_daily_stats_if_new_day()

_subscription_cache = {}
_subscription_cache_lock = threading.Lock()
SUBSCRIPTION_CACHE_TTL = 300  # 5 минут

def check_channel_subscription(user_id, force=False):
    """Проверяет подписку на канал. Раньше эта функция дёргала Telegram API
    (get_chat_member) на КАЖДОЕ действие пользователя, а любую ошибку — таймаут,
    сетевой сбой, flood-control при большом числе одновременных запросов —
    молча трактовала как "не подписан". Из-за этого при активном трафике реально
    подписанные люди периодически получали "подпишитесь на канал", хотя уже
    подписаны, а сам поток запросов на getChatMember только усугублял нагрузку.
    Теперь результат кэшируется на несколько минут (не дёргаем API на каждый клик),
    а если при живой проверке Telegram ответил ошибкой — используем последний
    известный результат вместо автоматического "нет". force=True — всегда живая
    проверка в обход кэша (нужно кнопке "Проверить" сразу после подписки)."""
    now = time.time()
    with _subscription_cache_lock:
        cached = _subscription_cache.get(user_id)
    if not force and cached and now - cached[1] < SUBSCRIPTION_CACHE_TTL:
        return cached[0]
    try:
        result = bot.get_chat_member(REQUIRED_CHANNEL, user_id).status in ['member', 'administrator', 'creator']
        with _subscription_cache_lock:
            _subscription_cache[user_id] = (result, now)
        return result
    except Exception as e:
        logger.warning(f"check_channel_subscription: не удалось проверить {user_id} ({e})")
        if cached:
            return cached[0]
        return False

_GOOD_BIGRAMS = {
    'th','he','in','er','an','re','on','at','en','nd','ti','es','or','te','of','ed','is','it',
    'al','ar','st','to','nt','ng','se','ha','as','ou','io','le','ve','co','me','de','hi','ri',
    'ro','ic','ne','ea','ra','ce','li','ch','ll','be','ma','si','om','ur','ca','el','ta','la',
    'ns','di','fo','ho','pe','ec','pr','no','ct','us','ac','ot','il','tr','ly','nc','et','id',
    'ol','ss','sc','mo','ba','ni','mi','po','we','do','wi','gh','ke','sp','am','ay','ir','ow',
    'wn','ck','nk','sh','ph','wh','gr','br','cr','dr','fr','pl','bl','cl','fl','gl','sl','sm',
    'sn','sw','sk','tw','qu','ob','rt','ki','ex','ad','un','ut','ub','ug','ud','uf','ul','um',
    'up','ig','ip','im','ib','ix','ev','ov','iv','av','ez','iz','oz','oe','ue','ie','oi','au',
    'aw','ey','oy','yl','yt','ys','yn','ym','yr'
}
_RARE_LETTERS = set('qxzj')

def rate_username(username):
    username = username.lower()
    length = len(username)
    bigrams = [username[i:i+2] for i in range(length - 1)]
    natural_ratio = (sum(1 for bg in bigrams if bg in _GOOD_BIGRAMS) / len(bigrams)) if bigrams else 0.0
    vowels = set('aeiou')
    alt_ratio = (
        sum(1 for i in range(length - 1) if (username[i] in vowels) != (username[i+1] in vowels)) / (length - 1)
        if length > 1 else 0.0
    )
    pronounceability = natural_ratio * 0.6 + alt_ratio * 0.4
    if length <= 5: length_bonus = 3
    elif length == 6: length_bonus = 2
    elif length == 7: length_bonus = 1
    elif length == 8: length_bonus = 0
    elif length <= 10: length_bonus = -1
    elif length <= 13: length_bonus = -2
    else: length_bonus = -3
    rare_penalty = sum(1 for c in username if c in _RARE_LETTERS) * 1.5
    repeat_penalty = 2 if re.search(r'(.)\1\1', username) else 0
    score = 1 + pronounceability * 8 + length_bonus - rare_penalty - repeat_penalty
    return max(1, min(10, round(score)))

def update_all_usernames():
    with db_lock:
        cursor.execute("SELECT user_id FROM users")
        for (uid,) in cursor.fetchall():
            try:
                cm = bot.get_chat_member(uid, uid)
                if cm.user.username: cursor.execute("UPDATE users SET username=? WHERE user_id=?", (cm.user.username, uid))
            except: pass
        conn.commit()

class TelegramSession:
    def __init__(self, db_id, phone, session_string=None):
        self.id=db_id; self.phone=phone; self.status='waiting'; self.session_string=session_string or ''
        self.client=None; self.is_connected=False; self.error_count=0; self.flood_until=None; self.last_used=0
    async def connect_client(self):
        if not self.session_string: self.status='invalid'; return False
        try:
            if not self.client:
                self.client = TelegramClient(StringSession(self.session_string), API_ID, API_HASH, loop=_async_loop)
            if not self.client.is_connected(): await self.client.connect()
            if await self.client.is_user_authorized(): self.is_connected=True; self.status='active'; return True
            else: self.status='invalid'; self.is_connected=False; return False
        except errors.FloodWaitError as e:
            self.is_connected = False
            self.status = 'flood'
            self.flood_until = moscow_now() + datetime.timedelta(seconds=max(int(e.seconds), 60))
            try: session_manager._note_flood()
            except Exception: pass
            try:
                with db_lock:
                    cursor.execute("UPDATE sessions SET status='flood', flood_until=?, updated_at=? WHERE id=?",
                                   (self.flood_until.strftime('%Y-%m-%d %H:%M:%S'), moscow_now().strftime('%Y-%m-%d %H:%M:%S'), self.id))
                    conn.commit()
            except Exception:
                pass
            return False
        except Exception as e:
            self.is_connected=False
            name = type(e).__name__
            if any(k in name for k in ('UserDeactivated', 'AuthKeyUnregistered', 'AuthKeyDuplicated',
                                        'SessionRevoked', 'SessionExpired', 'PhoneNumberBanned', 'Unauthorized')):
                self.status = 'invalid'
            else:
                self.status = 'waiting'
            return False
    async def disconnect_client(self):
        if self.client and self.client.is_connected():
            try: await self.client.disconnect()
            except: pass
        self.is_connected=False
    async def keep_alive(self):
        try:
            if not self.is_connected: await self.connect_client()
            if self.is_connected and self.status=='active':
                await self.client.send_message('me', random.choice(['ok','da','net']))
                self.last_used=time.time(); return True
        except Exception as e:
            # Раньше любая ошибка здесь молча проглатывалась (bare except: pass) и статус
            # 'active' не менялся — из-за этого забаненный/умерший аккаунт мог месяцами
            # висеть в списке как "Активна", а правда вскрывалась только на рестарте, когда
            # connect_client() заново проходит полную авторизацию. Теперь распознаём те же
            # признаки бана/протухания сессии прямо здесь, в реальном времени.
            name = type(e).__name__
            if any(k in name for k in ('UserDeactivated', 'AuthKeyUnregistered', 'AuthKeyDuplicated',
                                        'SessionRevoked', 'SessionExpired', 'PhoneNumberBanned', 'Unauthorized')):
                self.status = 'invalid'
            self.is_connected = False
        return False
    async def check_username(self, username):
        try:
            if not self.is_connected:
                if not await self.connect_client(): return "error"
            await asyncio.sleep(random.uniform(0.05, 0.15))
            try:
                r = await asyncio.wait_for(self.client(ResolveUsernameRequest(username)), timeout=15)
                return "taken"
            except errors.UsernameNotOccupiedError:
                # ResolveUsernameRequest уже дал авторитетный ответ: юзернейм НЕ занят.
                # CheckUsernameRequest ниже — вторичная проверка ("можно ли назначить
                # этот юзернейм СЕБЕ прямо сейчас"). Её ОШИБКИ/таймауты не означают "занят"
                # (временное ограничение на смену ника у конкретного аккаунта и т.п.) —
                # в этих случаях доверяем resolve. Но явный ответ False — это не ошибка,
                # а прямой сигнал от Telegram "нельзя назначить" (обычно означает, что
                # юзернейм забанен/зарезервирован Telegram) — раньше он молча
                # игнорировался и такие ники утекали как "free", хотя реально недоступны.
                try:
                    a = await asyncio.wait_for(self.client(CheckUsernameRequest(username)), timeout=15)
                    if not a:
                        logger.info(f"[session] @{username}: CheckUsernameRequest=False — ник забанен/недоступен для назначения")
                        return "banned"
                    return "free"
                except errors.UsernameOccupiedError:
                    return "taken"
                except errors.UsernameInvalidError:
                    return "banned"
                except errors.FloodWaitError as e: return f"flood:{e.seconds}"
                except asyncio.TimeoutError:
                    logger.warning(f"check_username CheckUsernameRequest timeout for {username} — доверяем resolve")
                    return "free"
                except Exception as e:
                    if 'FROZEN_METHOD_INVALID' in str(e):
                        return "frozen"
                    logger.warning(f"check_username CheckUsernameRequest error for {username}: {e!r} — доверяем resolve")
                    return "free"
            except errors.UsernameInvalidError: return "banned"
            except errors.FloodWaitError as e: return f"flood:{e.seconds}"
            except asyncio.TimeoutError:
                logger.warning(f"check_username ResolveUsernameRequest timeout for {username}")
                return "error"
            except Exception as e:
                if 'FROZEN_METHOD_INVALID' in str(e):
                    return "frozen"
                name = type(e).__name__
                if any(k in name for k in ('UserDeactivated', 'AuthKeyUnregistered', 'AuthKeyDuplicated',
                                            'SessionRevoked', 'SessionExpired', 'PhoneNumberBanned', 'Unauthorized')):
                    return "invalid"
                logger.warning(f"check_username error for {username}: {e!r}")
                return "error"
        except errors.FloodWaitError as e: return f"flood:{e.seconds}"
        except Exception as e:
            if 'FROZEN_METHOD_INVALID' in str(e):
                return "frozen"
            name = type(e).__name__
            if any(k in name for k in ('UserDeactivated', 'AuthKeyUnregistered', 'AuthKeyDuplicated',
                                        'SessionRevoked', 'SessionExpired', 'PhoneNumberBanned', 'Unauthorized')):
                return "invalid"
            logger.warning(f"check_username outer error for {username}: {e!r}")
            return "error"

class SessionManager:
    def __init__(self):
        self.all_sessions=[]; self.waiting_sessions=[]; self.lock=threading.RLock()
        self.stats={'checks_total':0,'checks_free':0,'checks_taken':0,'checks_banned':0,'checks_error':0}
        # Лимиты как в примере: MIN_DELAY=5с — минимальный интервал между двумя
        # проверками ОДНОЙ и той же сессии; GLOBAL_DELAY=1.5с — минимальный интервал
        # между любыми двумя выдачами сессии вообще (по всему пулу), даже если это
        # разные аккаунты. Вместе они не дают боту долбить Telegram слишком часто ни
        # с одного аккаунта, ни суммарно — и не дают проверкам зависать (обе паузы
        # считаются под коротким удержанием lock, а спим уже вне lock — см. ниже).
        self.last_check_time={}; self.MIN_DELAY=12.0
        self.GLOBAL_DELAY=3.0; self._last_global_check=0.0
        self.FLOOD_TIMEOUT=43200; self.max_active=MAX_ACTIVE_SESSIONS
        self.check_log={}
        self.SOFT_LIMIT=20; self.SOFT_WINDOW=300
        self.recent_floods=[]
        # Сессии, у которых прямо сейчас выполняется запрос к Telegram. get_next_session()
        # раньше "бронировал" сессию только по времени (last_check_time), а не по факту
        # занятости — если реальный запрос выполнялся дольше MIN_DELAY (обычное дело для
        # сетевого round-trip), другой параллельный verify_with_session() мог выбрать ТУ ЖЕ
        # сессию ещё до завершения первого запроса. Из-за этого один и тот же аккаунт мог
        # обслуживать два одновременных запроса к Telegram — что и создавало впечатление
        # "забаненная/зафлуженная сессия всё ещё проверяет" (второй запрос завершался уже
        # после того, как первый пометил сессию flood/banned).
        self.busy_ids=set()
        self._start_pinger(); self._start_stuck_checker(); self._start_flood_checker()
    def _start_pinger(self):
        def p():
            while True:
                time.sleep(600)
                with self.lock:
                    # Пингуем все сессии, у которых есть session_string, которые не
                    # заняты прямо сейчас (busy_ids) и не в статусе banned/invalid/flood.
                    to_ping = [s for s in self.all_sessions
                               if s.session_string and s.id not in self.busy_ids
                               and s.status not in ('banned', 'invalid', 'flood')]
                    for s in to_ping: self.busy_ids.add(s.id)
                for s in to_ping:
                    try:
                        if s.status != 'active':
                            run_async(s.connect_client())
                        run_async(s.keep_alive())
                    except Exception:
                        pass
                    finally:
                        with self.lock:
                            self.busy_ids.discard(s.id)
                            if s.status == 'waiting' and s.session_string and s not in self.waiting_sessions:
                                self.waiting_sessions.append(s)
                        try:
                            with db_lock:
                                cursor.execute("UPDATE sessions SET status=?, updated_at=? WHERE id=?",
                                               (s.status, moscow_now().strftime('%Y-%m-%d %H:%M:%S'), s.id))
                                conn.commit()
                        except Exception:
                            pass
        threading.Thread(target=p, daemon=True).start()
    def _start_stuck_checker(self):
        def sc():
            while True:
                time.sleep(600); self._fix_stuck_sessions()
        threading.Thread(target=sc, daemon=True).start()
    def _start_flood_checker(self):
        def fc():
            while True:
                time.sleep(30)
                to_clear = []
                with self.lock:
                    now = moscow_now()
                    for s in self.all_sessions:
                        if s.status=='flood' and s.flood_until and now >= s.flood_until:
                            s.status='waiting'
                            s.flood_until=None
                            s.error_count=0
                            if s.session_string and s not in self.waiting_sessions:
                                self.waiting_sessions.append(s)
                            self.last_check_time[s.id]=time.time()+self.MIN_DELAY
                            to_clear.append(s.id)
                if to_clear:
                    with db_lock:
                        cursor.executemany("UPDATE sessions SET status='waiting', flood_until=NULL, error_count=0, updated_at=? WHERE id=?",
                                            [(moscow_now().strftime('%Y-%m-%d %H:%M:%S'), sid) for sid in to_clear])
                        conn.commit()
                self._balance_sessions()
        threading.Thread(target=fc, daemon=True).start()
    def _fix_stuck_sessions(self):
        with self.lock:
            for s in self.all_sessions:
                if s.status=='waiting' and s not in self.waiting_sessions and s.session_string: self.waiting_sessions.append(s)
                if s.status=='active' and not s.is_connected and s.session_string:
                    s.status='waiting'
                    if s not in self.waiting_sessions: self.waiting_sessions.append(s)
        self._balance_sessions()
    def load_from_db(self):
        with db_lock:
            now = moscow_now()
            # banned и flood-сессии НЕ трогаем — их статус должен сохраняться между перезапусками
            cursor.execute("UPDATE sessions SET status='waiting', flood_until=NULL, error_count=0, updated_at=? WHERE status NOT IN ('invalid','banned','flood')", (now.strftime('%Y-%m-%d %H:%M:%S'),))
            conn.commit()
            cursor.execute("SELECT id, phone, session_string, status, flood_until, error_count FROM sessions")
            rows = cursor.fetchall()
        with self.lock:
            self.all_sessions=[]; self.waiting_sessions=[]
            for db_id, phone, ss, status, fu, ec in rows:
                s = TelegramSession(db_id, phone, session_string=ss)
                s.error_count = ec or 0
                if status == 'banned':
                    s.status = 'banned'
                elif status == 'flood' and fu:
                    flood_until = None
                    try:
                        flood_until = datetime.datetime.strptime(fu, '%Y-%m-%d %H:%M:%S').replace(tzinfo=MOSCOW_TZ)
                    except Exception:
                        flood_until = None
                    if flood_until and moscow_now() < flood_until:
                        s.status = 'flood'; s.flood_until = flood_until
                    else:
                        s.status = 'waiting'; s.error_count = 0
                        with db_lock: cursor.execute("UPDATE sessions SET status='waiting', flood_until=NULL, error_count=0, updated_at=? WHERE id=?", (now.strftime('%Y-%m-%d %H:%M:%S'), db_id)); conn.commit()
                else:
                    s.status = 'waiting'
                self.all_sessions.append(s)
                if s.status=='waiting' and s.session_string: self.waiting_sessions.append(s)
                self.last_check_time[s.id]=time.time()+self.MIN_DELAY
        self._balance_sessions()
    def _balance_sessions(self):
        ta = []
        to_disconnect = []
        with self.lock:
            active_sessions = [s for s in self.all_sessions if s.status=='active' and s.is_connected]
            if len(active_sessions) > self.max_active:
                for s in active_sessions[self.max_active:]:
                    s.status = 'waiting'
                    to_disconnect.append(s)
                    if s not in self.waiting_sessions: self.waiting_sessions.append(s)
            ac = sum(1 for s in self.all_sessions if s.status=='active' and s.is_connected)
            needed = self.max_active - ac
            if needed > 0:
                for s in self.waiting_sessions[:]:
                    if needed <= 0: break
                    if s.status=='waiting' and s.session_string and s not in to_disconnect: ta.append(s); self.waiting_sessions.remove(s); needed -= 1
                for s in ta: s.status='active'
        for s in to_disconnect:
            try: run_async(s.disconnect_client())
            except: pass
        for s in ta:
            try:
                c = run_async(s.connect_client())
                with db_lock: cursor.execute("UPDATE sessions SET status=?, updated_at=? WHERE id=?", (s.status, moscow_now().strftime('%Y-%m-%d %H:%M:%S'), s.id)); conn.commit()
                if not c and s.status == 'waiting':
                    with self.lock:
                        if s not in self.waiting_sessions: self.waiting_sessions.append(s)
            except Exception:
                s.status = 'waiting'
                with self.lock:
                    if s not in self.waiting_sessions: self.waiting_sessions.append(s)
    def _note_flood(self):
        with self.lock: self.recent_floods.append(time.time())
    def _effective_min_delay(self):
        now = time.time()
        with self.lock:
            self.recent_floods = [t for t in self.recent_floods if now - t < 600]
            n = len(self.recent_floods)
        if n == 0: return self.MIN_DELAY
        # чем больше флудов за последние 10 минут, тем сильнее притормаживаем весь пул —
        # плавная деградация вместо резкого удвоения даёт лучшее восстановление после всплеска банов
        return self.MIN_DELAY * min(1 + n * 1.5, 10.0)
    def _is_resting(self, session_id):
        now = time.time()
        log = self.check_log.setdefault(session_id, [])
        while log and now - log[0] > self.SOFT_WINDOW: log.pop(0)
        return len(log) >= self.SOFT_LIMIT
    def _log_check(self, session_id):
        self.check_log.setdefault(session_id, []).append(time.time())
    GET_SESSION_WAIT_CAP = 4.0
    def get_next_session(self):
        with self.lock:
            now = time.time()
            for s in self.all_sessions:
                if s.status=='flood' and s.flood_until and moscow_now() >= s.flood_until:
                    s.status='waiting'; s.flood_until=None; s.error_count=0
                    if s.session_string and s not in self.waiting_sessions: self.waiting_sessions.append(s)
                    self.last_check_time[s.id]=time.time()+self.MIN_DELAY
                    with db_lock: cursor.execute("UPDATE sessions SET status='waiting', flood_until=NULL, error_count=0, updated_at=? WHERE id=?", (moscow_now().strftime('%Y-%m-%d %H:%M:%S'), s.id)); conn.commit()
        self._balance_sessions()
        with self.lock:
            eff_delay = self._effective_min_delay()
            active = [s for s in self.all_sessions if s.status=='active' and s.is_connected
                      and not self._is_resting(s.id) and s.id not in self.busy_ids]
            if not active: return None
            oldest = min(active, key=lambda x: self.last_check_time.get(x.id, 0))
            wait = eff_delay - (now - self.last_check_time.get(oldest.id, 0))
            if wait < 0: wait = 0
            # GLOBAL_DELAY — минимальный интервал между ЛЮБЫМИ двумя выдачами сессии по
            # всему пулу (не только повтор одного аккаунта). Считаем максимум из двух пауз.
            global_wait = self.GLOBAL_DELAY - (now - self._last_global_check)
            if global_wait < 0: global_wait = 0
            wait = max(wait, global_wait)
            self.last_check_time[oldest.id] = now + wait + eff_delay
            self._last_global_check = now + wait
            oldest.last_used = now; self._log_check(oldest.id)
            self.busy_ids.add(oldest.id)
        if wait > 0: time.sleep(wait + 0.02)
        return oldest
    def release_session(self, session_id):
        """Снимает флаг 'занята прямо сейчас' после завершения запроса (успех/ошибка/таймаут —
        неважно как). Вызывать обязательно из finally в месте использования сессии."""
        with self.lock:
            self.busy_ids.discard(session_id)
    def mark_flood(self, session_id, seconds):
        target = None
        with self.lock:
            for s in self.all_sessions:
                if s.id == session_id:
                    # чем чаще конкретная сессия ловит FloodWait, тем дольше даём ей отдохнуть —
                    # так реже повторно долбим один и тот же аккаунт, который уже под подозрением у Telegram
                    penalty = min(1 + s.error_count * 0.5, 4.0)
                    real_wait = int(max(int(seconds), 60) * penalty)
                    s.status='flood'; s.flood_until=moscow_now()+datetime.timedelta(seconds=real_wait); s.error_count+=1
                    self.last_check_time[s.id]=time.time()+real_wait
                    s.is_connected=False
                    self.busy_ids.discard(s.id)
                    if s in self.waiting_sessions: self.waiting_sessions.remove(s)
                    target = s; break
        if target is None: return
        self._note_flood()
        try: run_async(target.disconnect_client())
        except: pass
        with db_lock: cursor.execute("UPDATE sessions SET status='flood', flood_until=?, error_count=error_count+1, updated_at=? WHERE id=?", (target.flood_until.strftime('%Y-%m-%d %H:%M:%S'), moscow_now().strftime('%Y-%m-%d %H:%M:%S'), session_id)); conn.commit()
        self._balance_sessions()
    def mark_frozen(self, session_id):
        target = None
        with self.lock:
            for s in self.all_sessions:
                if s.id == session_id:
                    s.status = 'banned'
                    s.is_connected = False
                    self.busy_ids.discard(s.id)
                    if s in self.waiting_sessions: self.waiting_sessions.remove(s)
                    target = s; break
        if target is None: return
        try: run_async(target.disconnect_client())
        except: pass
        with db_lock: cursor.execute("UPDATE sessions SET status='banned', updated_at=? WHERE id=?", (moscow_now().strftime('%Y-%m-%d %H:%M:%S'), session_id)); conn.commit()
        logger.warning(f"[session] сессия {session_id} заморожена Telegram (FROZEN_METHOD_INVALID) — помечена banned и убрана из пула")
        self._balance_sessions()
    def mark_invalid(self, session_id):
        """Помечает сессию как невалидную (протухла/забанена) сразу, как только это
        обнаружилось в реальном времени — а не только на следующем перезапуске бота."""
        target = None
        with self.lock:
            for s in self.all_sessions:
                if s.id == session_id:
                    s.status = 'invalid'
                    s.is_connected = False
                    self.busy_ids.discard(s.id)
                    if s in self.waiting_sessions: self.waiting_sessions.remove(s)
                    target = s; break
        if target is None: return
        try: run_async(target.disconnect_client())
        except: pass
        with db_lock: cursor.execute("UPDATE sessions SET status='invalid', updated_at=? WHERE id=?", (moscow_now().strftime('%Y-%m-%d %H:%M:%S'), session_id)); conn.commit()
        logger.warning(f"[session] сессия {session_id} помечена invalid (обнаружен бан/протухание в реальном времени)")
        self._balance_sessions()
    def remove_session(self, session_id):
        target = None
        with self.lock:
            for s in self.all_sessions[:]:
                if s.id == session_id:
                    target = s
                    self.all_sessions.remove(s)
                    if s in self.waiting_sessions: self.waiting_sessions.remove(s)
                    if s.id in self.last_check_time: del self.last_check_time[s.id]
                    self.busy_ids.discard(s.id)
                    break
        if target is not None:
            try: run_async(target.disconnect_client())
            except: pass
        with db_lock: cursor.execute("DELETE FROM sessions WHERE id=?", (session_id,)); conn.commit()
        self._balance_sessions()
    def get_status(self):
        with self.lock:
            return {"active": sum(1 for s in self.all_sessions if s.status=='active' and s.is_connected),
                    "flood": sum(1 for s in self.all_sessions if s.status=='flood'),
                    "waiting": sum(1 for s in self.all_sessions if s.status=='waiting'),
                    "invalid": sum(1 for s in self.all_sessions if s.status in ('invalid','banned')),
                    "total": len(self.all_sessions)}
    def has_active_sessions(self):
        with self.lock:
            return any(s.status == 'active' and s.is_connected for s in self.all_sessions)

session_manager = SessionManager()
session_manager.load_from_db()

def verify_with_session(username: str):
    """Возвращает True (подтверждённо свободен), False (подтверждённо занят/забанен)
    или None (сессия не ответила вовремя / пул сессий сейчас занят — неизвестно)."""
    username = username.strip().replace('@', '').lower()
    if len(username) < 5 or len(username) > 32:
        return False
    for attempt in range(3):
        session = session_manager.get_next_session()
        if not session:
            return None  # сессий сейчас нет — неизвестно, а не "занято"
        with session_manager.lock:
            session_manager.stats['checks_total'] += 1
        try:
            try:
                result = run_async(session.check_username(username), timeout=15)
            except TimeoutError:
                logger.warning(f"[session] @{username}: сессия {session.id} не ответила вовремя")
                continue
            logger.info(f"[session] @{username}: сессия {session.id} -> {result}")
            if result == "free":
                with session_manager.lock: session_manager.stats['checks_free'] += 1
                return True
            elif result in ("taken", "banned"):
                with session_manager.lock: session_manager.stats['checks_taken' if result == "taken" else 'checks_banned'] += 1
                return False
            elif isinstance(result, str) and result.startswith("flood:"):
                try: secs = int(result.split(":")[1])
                except: secs = 60
                session_manager.mark_flood(session.id, min(secs, 6 * 3600))
                with session_manager.lock: session_manager.stats['checks_error'] += 1
                continue
            elif result == "frozen":
                session_manager.mark_frozen(session.id)
                with session_manager.lock: session_manager.stats['checks_error'] += 1
                continue
            elif result == "invalid":
                session_manager.mark_invalid(session.id)
                with session_manager.lock: session_manager.stats['checks_error'] += 1
                continue
            else:
                with session_manager.lock: session_manager.stats['checks_error'] += 1
                continue
        finally:
            # Обязательно снимаем busy-флаг, каким бы путём мы ни вышли из try (return/continue/
            # исключение) — иначе сессия навсегда "зависнет" занятой и выпадет из пула.
            session_manager.release_session(session.id)
    return None  # 3 попытки не дали чёткого ответа — неизвестно, а не "занято"

_http_session = requests.Session()
_http_retry = Retry(total=0, connect=0, read=0, backoff_factor=0.1,
                     status_forcelist=[502, 503, 504], allowed_methods=frozenset(['GET', 'POST']))
_http_adapter = HTTPAdapter(pool_connections=150, pool_maxsize=150, max_retries=_http_retry)
_http_session.mount('https://', _http_adapter)
_http_session.mount('http://', _http_adapter)

# Ограничители конкурентности для веб-проверки (перенесено из "быстрой" версии чекера):
# FRAGMENT_MAX_CONCURRENT — не более N одновременных запросов к fragment.com (он куда
# строже к нагрузке, чем t.me, и легче банит/капчит при параллельных запросах).
# GLOBAL_CHECK_CONCURRENCY — общий потолок одновременных полных проверок (t.me [+ fragment])
# по всему боту сразу, независимо от того, сколько поисков сейчас идёт параллельно —
# защищает от захлёбывания исходящих соединений при резком всплеске CHECK_WORKERS.
FRAGMENT_MAX_CONCURRENT = 10
_fragment_semaphore = threading.BoundedSemaphore(FRAGMENT_MAX_CONCURRENT)
GLOBAL_CHECK_CONCURRENCY = 60
_global_check_semaphore = threading.BoundedSemaphore(GLOBAL_CHECK_CONCURRENCY)

class UsernameChecker:
    HEADERS = {
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
        'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
        'Accept-Language': 'en-US,en;q=0.5',
        'Cache-Control': 'no-cache',
        'Pragma': 'no-cache',
    }
    RESERVED = {'telegram', 'admin', 'support', 'security', 'contact', 'settings',
                'username', 'bot', 'api', 'login', 'help', 'faq', 'terms', 'privacy',
                'about', 'blog', 'jobs', 'press', 'brand', 'sticker', 'stickers'}

    _TITLE_RE = re.compile(r'<title>(.*?)</title>', re.IGNORECASE | re.DOTALL)
    _SCRIPT_STYLE_RE = re.compile(r'<(script|style)[^>]*>.*?</\1>', re.IGNORECASE | re.DOTALL)
    _TAG_RE = re.compile(r'<[^>]+>')
    _WS_RE = re.compile(r'\s+')

    def __init__(self, delay=0):
        self.cache = {}
        self.cache_lock = threading.Lock()
        self.cache_ttl = 300
        self._rate_limit_times = {}
        self._rate_limit_lock = threading.Lock()
        self.min_interval = 0.033

    def _rate_limit(self, key):
        with self._rate_limit_lock:
            now = time.time()
            if key in self._rate_limit_times:
                elapsed = now - self._rate_limit_times[key]
                if elapsed < self.min_interval:
                    time.sleep(self.min_interval - elapsed)
            self._rate_limit_times[key] = time.time()

    @staticmethod
    def _html_structure_metrics(html_text):
        stripped = UsernameChecker._SCRIPT_STYLE_RE.sub('', html_text)
        div_count = len(re.findall(r'<div[\s>]', stripped, re.IGNORECASE))
        a_count = len(re.findall(r'<a[\s>]', stripped, re.IGNORECASE))
        clean_text = UsernameChecker._WS_RE.sub(' ', UsernameChecker._TAG_RE.sub(' ', stripped)).strip()
        return div_count, a_count, len(clean_text)

    def check_telegram_web(self, username):
        """Возвращает 'taken', 'free' или 'error' (НЕ 'free' на любую не-200/сбой —
        это и было источником ложных 'свободен' на забаненном/заблокированном IP)."""
        self._rate_limit('t.me')
        try:
            r = _fetch_direct(f"https://t.me/{username}", headers=self.HEADERS, timeout=REQUEST_TIMEOUT)
        except Exception as e:
            logger.warning(f"t.me error for @{username}: {e}")
            return 'error'
        if r.status_code != 200:
            # 403/429/капча/редирект антибота с заблокированного IP — НЕИЗВЕСТНО,
            # а не 'free'. Раньше именно эта ветка отдавала занятые/забаненные ники.
            logger.warning(f"t.me @{username}: unexpected status {r.status_code}")
            return 'error'
        text = r.text.lower()
        if 'tgme_page_title' in text:
            return 'taken'
        m = self._TITLE_RE.search(r.text)
        if m and ': view @' in m.group(1).strip().lower():
            return 'taken'
        div_count, a_count, clean_len = self._html_structure_metrics(r.text)
        if div_count >= 12 and a_count >= 5:
            return 'taken'
        return 'free'

    def check_fragment(self, username):
        """Возвращает 'taken', 'free' или 'error' (НЕ 'free' на сбой/таймаут)."""
        self._rate_limit('fragment')
        if not _fragment_semaphore.acquire(timeout=6):
            logger.warning(f"Fragment semaphore timeout for @{username}")
            return 'error'
        try:
            r = _fetch_direct(f"https://fragment.com/username/{username}",
                                        headers=self.HEADERS, timeout=4, allow_redirects=True)
        except Exception as e:
            logger.warning(f"Fragment error for @{username}: {e}")
            return 'error'
        finally:
            _fragment_semaphore.release()
        if r.status_code != 200:
            return 'error'
        text = r.text.lower()
        if "query=" in r.url:
            return 'free'
        if "auction" in text or "make an offer" in text or "for sale" in text:
            return 'taken'
        return 'free'

    def check(self, username, use_cache=True, use_fragment=True):
        """Tri-state: True (подтверждённо свободен по t.me+fragment), False (занят/
        забанен/выставлен на аукцион), None (неизвестно — сеть не ответила чётко).
        None НИКОГДА не трактуется как 'free' — это обязанность passes_checks:
        без сессионного подтверждения None-кандидат не выдаётся."""
        username = username.strip().lstrip('@').lower()
        if not self.is_valid_format(username):
            return False

        if use_cache:
            with self.cache_lock:
                if username in self.cache:
                    t, result = self.cache[username]
                    if time.time() - t < self.cache_ttl:
                        return result

        if not _global_check_semaphore.acquire(timeout=25):
            return None
        try:
            tme_result = self.check_telegram_web(username)
            if tme_result == 'taken':
                self._set_cache(username, False)
                return False
            if tme_result == 'error':
                return None  # неизвестно — НЕ free

            if not use_fragment:
                self._set_cache(username, True)
                return True

            fragment_result = self.check_fragment(username)
            if fragment_result == 'taken':
                self._set_cache(username, False)
                return False
            if fragment_result == 'error':
                return None  # t.me сказал free, fragment не ответил — всё равно неизвестно

            self._set_cache(username, True)
            return True
        finally:
            _global_check_semaphore.release()

    def _set_cache(self, username, value):
        with self.cache_lock:
            if len(self.cache) > 10000:
                self.cache.clear()
            self.cache[username] = (time.time(), value)

    def is_valid_format(self, username):
        username = username.lstrip('@').lower()
        if not (5 <= len(username) <= 32):
            return False
        if not re.match(r'^[a-z][a-z0-9_]*[a-z0-9]$', username):
            return False
        if '__' in username:
            return False
        if username in self.RESERVED:
            return False
        return True

    def clear_cache(self):
        with self.cache_lock:
            self.cache.clear()

checker = UsernameChecker()

_session_verify_semaphore = threading.Semaphore(1)

class SessionVerifyBudget:
    """Отдельный бюджет на дорогие проверки через Telegram-сессию в рамках одного поиска.
    HTTP+fragment проверка (checker.check) в этот бюджет не входит — она дешёвая и гоняется свободно/параллельно."""
    __slots__ = ('limit', 'count', 'lock', 'found_event')
    def __init__(self, limit=SESSION_VERIFY_LIMIT):
        self.limit = limit; self.count = 0; self.lock = threading.Lock()
        self.found_event = threading.Event()
    def try_consume(self):
        with self.lock:
            if self.count >= self.limit: return False
            self.count += 1; return True

def passes_checks(user_id, username, budget):
    if budget.found_event.is_set():
        return False

    http_result = checker.check(username)

    if http_result is False:
        add_rejected(user_id)
        return False

    if http_result is True:
        # Bot API не умеет отличить забаненный/зарезервированный ник от реально
        # свободного — оба дают "chat not found". Поэтому "свободен" от Bot API
        # НИКОГДА не принимается сам по себе — только как повод дёрнуть сессию.
        if not session_manager.has_active_sessions():
            return False
        if not budget.try_consume():
            return False  # бюджет сессий исчерпан — не доверяем одному Bot API, пропускаем
        if not _session_verify_semaphore.acquire(timeout=5):
            return False
        try:
            verified = verify_with_session(username)
            if verified is True:
                budget.found_event.set()
                return True
            elif verified is False:
                add_rejected(user_id)
                return False
            return False  # сессия не ответила (None) — не отдаём без подтверждения
        finally:
            _session_verify_semaphore.release()

    if not session_manager.has_active_sessions():
        return False
    if not budget.try_consume():
        return False
    if not _session_verify_semaphore.acquire(timeout=5):
        return False
    try:
        verified = verify_with_session(username)
        if verified is False:
            add_rejected(user_id)
            return False
        if verified is None:
            return False
        budget.found_event.set()
        return True
    finally:
        _session_verify_semaphore.release()

def get_user(user_id):
    with db_lock:
        cursor.execute("SELECT * FROM users WHERE user_id=?", (user_id,))
        row = cursor.fetchone()
        if row: return dict(zip([desc[0] for desc in cursor.description], row))
        return None

def get_user_by_id(user_id):
    return get_user(user_id)

def create_user(user_id, username=None, referrer_id=None):
    with db_lock:
        cursor.execute("SELECT * FROM users WHERE user_id=?", (user_id,))
        if cursor.fetchone(): return get_user(user_id), False
        now = moscow_now().strftime('%Y-%m-%d %H:%M:%S')
        cursor.execute('INSERT INTO users (user_id, username, referrer_id, created_date) VALUES (?,?,?,?)', (user_id, username, referrer_id, now))
        conn.commit()
        return get_user(user_id), True

def update_user(user_id, **kwargs):
    allowed = {'username','referrer_id','referrals_count','last_search_date','total_searches','found_count','rejected_count','subscribed','referral_activated','banned','search_mode','is_premium','premium_expires','daily_searches','last_search_reset','premium_source'}
    with db_lock:
        for k, v in kwargs.items():
            if k in allowed: cursor.execute(f"UPDATE users SET {k}=? WHERE user_id=?", (v, user_id))
        conn.commit()

def is_banned(user_id):
    user = get_user(user_id)
    return user and user.get('banned',0) == 1

def has_premium(user_id):
    """Премиум активен, если срок не истёк. Если премиум получен по промокоду
    (premium_source == 'promo'), дополнительно требуется юзернейм бота в имени
    профиля: без него премиум временно отключается (is_premium=0), но
    premium_expires НЕ трогается — срок продолжает идти. Если премиум получен
    не по промокоду (покупка, реферал, выдача админом) — юзернейм не требуется."""
    user = get_user(user_id)
    if not user:
        return False
    expires = user.get('premium_expires')
    if not expires:
        return user.get('is_premium', 0) == 1
    try:
        exp_dt = datetime.datetime.strptime(expires, '%Y-%m-%d %H:%M:%S').replace(tzinfo=MOSCOW_TZ)
    except Exception:
        return user.get('is_premium', 0) == 1
    if moscow_now() >= exp_dt:
        if user.get('is_premium', 0) == 1 or user.get('premium_expires') or user.get('premium_source'):
            update_user(user_id, is_premium=0, premium_expires=None, premium_source=None)
        return False
    if user.get('premium_source') == 'promo' and not _bot_username_in_name(user_id):
        if user.get('is_premium', 0) == 1:
            update_user(user_id, is_premium=0)
        return False
    if user.get('is_premium', 0) != 1:
        update_user(user_id, is_premium=1)
    return True

def reset_daily_searches_if_needed(user_id):
    user = get_user(user_id)
    if not user: return
    today = moscow_now().strftime('%Y-%m-%d')
    last_reset = user.get('last_search_reset')
    if last_reset != today:
        update_user(user_id, daily_searches=0, last_search_reset=today)

def free_searches_left(user_id):
    reset_daily_searches_if_needed(user_id)
    user = get_user(user_id)
    used = (user.get('daily_searches') or 0) if user else 0
    return max(0, FREE_DAILY_SEARCHES - used)

def can_search(user_id):
    """Премиум — без ограничений. Иначе доступно FREE_DAILY_SEARCHES бесплатных поисков в сутки."""
    if has_premium(user_id):
        return True
    return free_searches_left(user_id) > 0

def consume_search(user_id):
    """Списывает один бесплатный поиск. У премиум-пользователей расход не ведётся."""
    if has_premium(user_id):
        return
    increment_daily_search(user_id)

def no_search_left_text(user_id):
    if has_premium(user_id):
        return f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Что-то пошло не так с проверкой премиума. Попробуй ещё раз чуть позже.</b>"
    return (f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Бесплатные поиски на сегодня закончились ({FREE_DAILY_SEARCHES}/день).</b>\n\n"
            f"<blockquote>Новые бесплатные поиски придут завтра, либо оформи премиум в разделе «Премиум», чтобы искать без ограничений.</blockquote>\n\n"
            f"{premium_benefits_text()}")

def _days_in_bot(user):
    """Сколько дней пользователь в боте, по created_date. Общая логика для
    экрана «Профиль» в боте и для /api/profile."""
    reg_date = user.get('created_date') if user else None
    if not reg_date:
        return 0
    try:
        reg_dt = datetime.datetime.strptime(reg_date, '%Y-%m-%d %H:%M:%S').replace(tzinfo=MOSCOW_TZ)
        return (moscow_now() - reg_dt).days
    except Exception:
        return 0

def get_user_by_username(username):
    with db_lock:
        cursor.execute("SELECT user_id FROM users WHERE LOWER(username)=LOWER(?)", (username.replace('@',''),))
        row = cursor.fetchone()
        if row: return row[0]
    return None

user_found_cooldown = {}
FOUND_COOLDOWN_SECONDS = 3

active_username_checks = set()
active_username_checks_lock = threading.Lock()
BUSY_CHECK_TEXT = "⏳ Дождитесь окончания текущей проверки юзернейма."
OVERLOAD_TEXT = f"<tg-emoji emoji-id='{E_MAIN}'>🔥</tg-emoji> Сейчас слишком много одновременных поисков. Попробуйте через несколько секунд."

# Реальная пропускная способность сессионной проверки жёстко ограничена физикой:
# MAX_ACTIVE_SESSIONS аккаунтов, каждый не чаще раза в MIN_DELAY секунд — то есть
# ~ MAX_ACTIVE_SESSIONS / MIN_DELAY подтверждений в секунду НА ВЕСЬ бот, а не на пользователя.
# При MAX_ACTIVE_SESSIONS=10 и MIN_DELAY=5с это ~2 проверки/сек суммарно по всем поискам.
# Раньше лимита на кол-во одновременных поисков не было вообще: при 20+ активных людях все
# их воркеры (до CHECK_WORKERS * кол-во поисков потоков) вместе не давали 20 участникам,
# каждый поиск буквально доживал все SEARCH_TIME_BUDGET=30с секунд, не успевая получить
# ни одной сессионной проверки — отсюда "долго ищет и ничего не находит".
# Ограничиваем число поисков, идущих ОДНОВРЕМЕННО, чтобы админиттед-поиски реально получали
# сессионные проверки в течение своего окна, а не голодали все вместе.
# Формула ориентировочная: (пропускная способность * окно поиска) / ~4 попыток на поиск.
MAX_CONCURRENT_SEARCHES = max(5, (MAX_ACTIVE_SESSIONS * 6))

def try_start_check(user_id):
    with active_username_checks_lock:
        if user_id in active_username_checks:
            return False, 'already_running'
        if len(active_username_checks) >= MAX_CONCURRENT_SEARCHES:
            return False, 'overload'
        active_username_checks.add(user_id)
    return True, None

def end_check(user_id):
    with active_username_checks_lock:
        active_username_checks.discard(user_id)

HARD_SEARCH_TIMEOUT = 60
search_cancel_events = {}
search_state_lock = threading.Lock()

def register_search(user_id, chat_id, message_id):
    ev = threading.Event()
    with search_state_lock:
        search_cancel_events[user_id] = ev
    def watchdog():
        if ev.wait(HARD_SEARCH_TIMEOUT):
            return
        ev.set()
        with active_username_checks_lock:
            was_active = user_id in active_username_checks
            active_username_checks.discard(user_id)
        if was_active:
            fail_markup = types.InlineKeyboardMarkup(row_width=1)
            fail_markup.add(btn("Попробовать ещё раз", callback_data="search_back_to_menu", emoji=E_PROMO_SEARCH, style="primary"))
            try:
                bot.edit_message_text(
                    f"<b><tg-emoji emoji-id='{E_WARN}'>⏱</tg-emoji> Поиск занял слишком много времени и был остановлен.</b>\n\n"
                    f"<i>Попробуйте запустить поиск заново.</i>",
                    chat_id, message_id, parse_mode='HTML', reply_markup=fail_markup)
            except Exception:
                pass
    threading.Thread(target=watchdog, daemon=True).start()
    return ev

def unregister_search(user_id, ev):
    ev.set()
    with search_state_lock:
        if search_cancel_events.get(user_id) is ev:
            del search_cancel_events[user_id]

def cancel_markup():
    m = types.InlineKeyboardMarkup(row_width=1)
    m.add(btn("Отмена", callback_data="search_cancel", emoji=E_WARN, style="danger"))
    return m

@bot.callback_query_handler(func=lambda call: call.data == "search_cancel")
def search_cancel_handler(call):
    user_id = call.from_user.id
    with search_state_lock:
        ev = search_cancel_events.get(user_id)
    if ev:
        ev.set()
        try: bot.answer_callback_query(call.id, "Отменяю поиск...")
        except: pass
        return
    # ev нет — поиск ещё не дошёл до register_search (завис раньше: на db_lock,
    # на сетевом вызове к Telegram и т.п.). Раньше кнопка отмены в этом случае
    # ничего не могла сделать, и пользователь был обречён ждать HARD_SEARCH_TIMEOUT
    # (или вечно, если сам этот watchdog ещё не стартовал). Раз пользователь явно
    # просит отменить — снимаем статус "занят" сразу.
    with active_username_checks_lock:
        was_active = user_id in active_username_checks
        active_username_checks.discard(user_id)
    try: bot.answer_callback_query(call.id, "Поиск сброшен" if was_active else "Отменяю поиск...")
    except: pass

def start_hard_release_watchdog(user_id, chat_id):
    """Независимый от register_search watchdog. Раньше защита от зависания
    (HARD_SEARCH_TIMEOUT) стартовала только ВНУТРИ perform_search/process_*, уже
    после DB-запросов и первого bot.send_message — если зависало раньше этого
    момента (db_lock, сетевой вызов к Telegram и т.п.), watchdog просто не успевал
    создаться, и пользователь застревал на BUSY_CHECK_TEXT навсегда, до перезапуска
    бота. Эта версия стартует СРАЗУ, как только try_start_check() отметил
    пользователя занятым — до входа в саму функцию поиска.
    Вызывающий код обязан выставить возвращённый Event в finally после завершения
    поиска (любым путём) — иначе через HARD_SEARCH_TIMEOUT статус сбросится
    принудительно и пользователю придёт уведомление."""
    ev = threading.Event()
    def _watch():
        if ev.wait(HARD_SEARCH_TIMEOUT):
            return
        with active_username_checks_lock:
            was_active = user_id in active_username_checks
            active_username_checks.discard(user_id)
        if was_active:
            try:
                bot.send_message(chat_id, "<b>⏱ Поиск завис и был сброшен. Попробуйте запустить его заново.</b>", parse_mode='HTML')
            except Exception:
                pass
    threading.Thread(target=_watch, daemon=True).start()
    return ev

def get_search_cooldown_remaining(user_id):
    last = user_found_cooldown.get(user_id, 0)
    remaining = FOUND_COOLDOWN_SECONDS - (time.time() - last)
    return max(0, remaining)

def add_found(user_id):
    user_found_cooldown[user_id] = time.time()
    user = get_user(user_id)
    if user: update_user(user_id, found_count=(user.get('found_count',0)+1), last_search_date=moscow_now().strftime('%Y-%m-%d'))

def increment_daily_search(user_id):
    reset_daily_searches_if_needed(user_id)
    user = get_user(user_id)
    if user:
        update_user(user_id, daily_searches=(user.get('daily_searches') or 0) + 1)

def add_rejected(user_id):
    user = get_user(user_id)
    if user: update_user(user_id, rejected_count=(user.get('rejected_count',0)+1), last_search_date=moscow_now().strftime('%Y-%m-%d'))

def record_found_username(user_id, username, length, user=None):
    """Фиксирует найденный юзернейм. Раньше это было 4 отдельных commit() подряд
    (found_count, дневной лимит поисков, INSERT INTO found, total_searches) —
    под нагрузкой каждый из них по очереди держал общий db_lock и блокировал
    ВСЕХ остальных активных пользователей, отсюда заметный лаг именно в момент
    находки. Теперь всё это — один SELECT и один commit."""
    if user is None:
        user = get_user(user_id)
    is_prem = has_premium(user_id)
    today = moscow_now().strftime('%Y-%m-%d')
    now_str = moscow_now().strftime('%Y-%m-%d %H:%M:%S')
    rating = rate_username(username)
    user_found_cooldown[user_id] = time.time()
    with db_lock:
        found_count = (user.get('found_count', 0) if user else 0) + 1
        total_searches = (user.get('total_searches', 0) if user else 0) + 1
        params = {'found_count': found_count, 'last_search_date': today, 'total_searches': total_searches}
        if not is_prem:
            last_reset = user.get('last_search_reset') if user else None
            daily_searches = (user.get('daily_searches') or 0) if user else 0
            if last_reset != today:
                daily_searches = 0
            params['daily_searches'] = daily_searches + 1
            params['last_search_reset'] = today
        set_clause = ', '.join(f"{k}=?" for k in params)
        cursor.execute(f"UPDATE users SET {set_clause} WHERE user_id=?", (*params.values(), user_id))
        try:
            cursor.execute("INSERT OR IGNORE INTO found (username, length, price, found_date, finder_id) VALUES (?,?,?,?,?)", (username, length, f"{rating}/10", now_str, user_id))
        except Exception:
            pass
        conn.commit()
    user_last_action[user_id] = time.time()
    return rating

def stock_add(username, length, mode):
    """Кладёт 'лишний' найденный ник в пул — уже проверенный сессией, ждёт следующего поиска."""
    try:
        with db_lock:
            cursor.execute("INSERT OR IGNORE INTO username_stock (username, length, mode, created_at) VALUES (?,?,?,?)",
                           (username, length, mode, moscow_now().strftime('%Y-%m-%d %H:%M:%S')))
            conn.commit()
    except Exception:
        pass

def stock_remove(username):
    try:
        with db_lock:
            cursor.execute("DELETE FROM username_stock WHERE username=?", (username,))
            conn.commit()
    except Exception:
        pass

STOCK_MAX_AGE = datetime.timedelta(hours=3)

def stock_take(length, mode):
    """Атомарно забирает один ник из пула под нужные длину/режим, либо None если пусто.
    Ники старше STOCK_MAX_AGE считаем протухшими (за это время их могли забрать вручную
    в Telegram) и просто выкидываем, не выдавая пользователю без повторной проверки."""
    now = moscow_now()
    with db_lock:
        while True:
            cursor.execute("SELECT username, created_at FROM username_stock WHERE length=? AND mode=? ORDER BY created_at LIMIT 1", (length, mode))
            row = cursor.fetchone()
            if not row:
                return None
            username, created_at = row
            cursor.execute("DELETE FROM username_stock WHERE username=?", (username,))
            stale = False
            try:
                created_dt = datetime.datetime.strptime(created_at, '%Y-%m-%d %H:%M:%S').replace(tzinfo=MOSCOW_TZ)
                stale = (now - created_dt) > STOCK_MAX_AGE
            except Exception:
                pass
            conn.commit()
            if not stale:
                return username
            # протухший — удалили, пробуем следующий

def stock_count():
    with db_lock:
        cursor.execute("SELECT COUNT(*) FROM username_stock")
        return cursor.fetchone()[0]

def stock_list(limit=30):
    with db_lock:
        cursor.execute("SELECT username, length, mode, created_at FROM username_stock ORDER BY created_at DESC LIMIT ?", (limit,))
        return cursor.fetchall()

def stock_clear():
    with db_lock:
        cursor.execute("DELETE FROM username_stock")
        conn.commit()

def check_subscription(user_id, force=False):
    return check_channel_subscription(user_id, force=force)

def subscription_required(func):
    def wrapper(call_or_msg):
        user_id = call_or_msg.from_user.id
        if MAINTENANCE_MODE and user_id != ADMIN_ID:
            bot.send_message(user_id, f"<b><tg-emoji emoji-id='{E_TECH_WORKS_TITLE}'>🔧</tg-emoji> Использование бота невозможно.</b>\n\n<blockquote><b><tg-emoji emoji-id='{E_TECH_WORKS}'>🛠</tg-emoji> Проводяться технические работы.</b></blockquote>", parse_mode='HTML')
            return
        if is_banned(user_id):
            bot.send_message(user_id, f"<b><tg-emoji emoji-id='{E_BANNED}'>🚫</tg-emoji> Извините, но вы заблокированы.</b>\n\n<blockquote><b><tg-emoji emoji-id='{E_BANNED_REASON}'>📝</tg-emoji> Можете написать владельцу @nuemc, объяснить ситуацию, и попросить разбанить</b></blockquote>", parse_mode='HTML')
            return
        if check_subscription(user_id): return func(call_or_msg)
        else:
            text = (f"<b><tg-emoji emoji-id='{E_ACCESS_DENIED}'>🔒</tg-emoji> Доступ к боту ограничен.</b>\n\n"
                    f"<blockquote><b><tg-emoji emoji-id='{E_ACCESS_CHANNEL}'>📢</tg-emoji> Чтобы использовать бота нужно подписаться на канал. затем нажать на кнопку проверки.</b></blockquote>")
            markup = types.InlineKeyboardMarkup(row_width=1)
            markup.add(btn("Подписаться", url=CHANNEL_LINK, emoji=E_CHANNEL_LABEL, style="primary"), btn("Проверить", callback_data="check_sub", emoji=E_PROMO_OK, style="success"))
            bot.send_message(user_id, text, parse_mode='HTML', reply_markup=markup)
    return wrapper

def premium_upsell_markup():
    """Кнопка, которая ведёт в раздел «Премиум» самого бота — чтобы пользователь
    оформлял премиум там (звёзды/крипта), а не писал напрямую владельцу."""
    markup = types.InlineKeyboardMarkup(row_width=1)
    markup.add(btn("Открыть «Премиум»", callback_data="open_premium_menu", emoji=E_PREMIUM, style="primary"))
    return markup

def premium_benefits_text():
    """Короткий список того, что даёт премиум — используется и в меню «Премиум»,
    и в сообщении о том, что бесплатные попытки закончились."""
    return (f"<b><tg-emoji emoji-id='{E_WHAT}'>💎</tg-emoji> Что даёт премиум:</b>\n"
            f"<blockquote><b><tg-emoji emoji-id='{E_INFO_LIST}'>▫️</tg-emoji> Безлимитные поиски</b> — без ограничения {FREE_DAILY_SEARCHES}/день\n"
            f"<b><tg-emoji emoji-id='{E_INFO_LIST}'>▫️</tg-emoji> Никакого ожидания</b> — не нужно ждать завтрашнего сброса лимита\n"
            f"<b><tg-emoji emoji-id='{E_INFO_LIST}'>▫️</tg-emoji> Ищи сколько угодно</b> — по слову и по фильтру без остановки</blockquote>\n\n")

def send_premium_menu(user_id):
    is_prem = has_premium(user_id)
    status_line = f"<tg-emoji emoji-id='{E_FOUND_NICK}'>✅</tg-emoji> Активен" if is_prem else f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Не активен"
    crypto_price = get_crypto_day_price()
    text = (f"<b><tg-emoji emoji-id='{E_PREMIUM}'>⭐</tg-emoji> Премиум</b>\n\n"
            f"<b>Твой статус:</b> {status_line}\n\n"
            f"{premium_benefits_text()}"
            f"<blockquote><b>1 день — {PRIEMKA_STARS_PER_DAY} <tg-emoji emoji-id='{E_PREMIUM}'>⭐</tg-emoji> (Telegram Stars)</b>\n"
            f"<b>1 день — {crypto_price}$ (криптовалютой)</b></blockquote>\n\n")
    markup = types.InlineKeyboardMarkup(row_width=1)
    if PRIEMKA_ENABLED and PRIEMKA_USERNAME:
        text += (f"<b><tg-emoji emoji-id='{E_PLANE}'>🎁</tg-emoji> Чтобы оплатить звёздами:</b>\n"
                 f"<blockquote>1. Нажми «Отправить звёзды»\n"
                 f"2. Отправь подарок (звёзды) на открывшийся аккаунт — можно 25, 50 или 100 <tg-emoji emoji-id='{E_PREMIUM}'>⭐</tg-emoji>\n"
                 f"3. Премиум зачислится автоматически в течение минуты, из расчёта {PRIEMKA_STARS_PER_DAY}<tg-emoji emoji-id='{E_PREMIUM}'>⭐</tg-emoji> = 1 день</blockquote>\n\n")
        markup.add(btn("Отправить звёзды", url=f"https://t.me/{PRIEMKA_USERNAME}", emoji=E_PROMO_STAR, style="primary"))
    else:
        text += "<i>Оплата звёздами временно недоступна</i>"
    markup.add(btn("Оплатить криптовалютой", callback_data="crypto_buy", emoji=E_PROMO_STAR2, style="primary"))
    bot.send_message(user_id, text, parse_mode='HTML', reply_markup=markup)

@bot.message_handler(func=lambda m: m.text == "Премиум")
@subscription_required
def premium_menu_handler(message):
    user_id = message.from_user.id
    user_last_action[user_id] = time.time()
    send_premium_menu(user_id)

@bot.callback_query_handler(func=lambda call: call.data == "open_premium_menu")
def open_premium_menu_callback(call):
    bot.answer_callback_query(call.id)
    send_premium_menu(call.from_user.id)

@bot.callback_query_handler(func=lambda call: call.data == "crypto_buy")
def crypto_buy_callback(call):
    bot.answer_callback_query(call.id)
    user_id = call.from_user.id
    days = 1
    pay_url, invoice_id = create_crypto_invoice(user_id, days)
    if not pay_url:
        bot.send_message(call.message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Не удалось создать счёт на оплату. Попробуйте позже.\n<i>{invoice_id}</i>", parse_mode='HTML')
        return
    crypto_price = get_crypto_day_price()
    amount = round(days * crypto_price, 2)
    markup = types.InlineKeyboardMarkup(row_width=1)
    markup.add(btn(f"Оплатить {amount}$", url=pay_url, emoji=E_PROMO_STAR, style="primary"))
    bot.send_message(call.message.chat.id, f"<b>Счёт создан</b>\n\nК оплате: {amount}$ ({days} дн. премиума)\n\nПосле оплаты премиум зачислится автоматически в течение минуты.", parse_mode='HTML', reply_markup=markup)

@bot.callback_query_handler(func=lambda call: call.data == "check_sub")
def check_sub_callback(call):
    if check_subscription(call.from_user.id, force=True):
        bot.answer_callback_query(call.id)
        activate_referral(call.from_user.id)
        bot.delete_message(call.message.chat.id, call.message.message_id)
        bot.send_message(call.from_user.id, f"<b><tg-emoji emoji-id='{E_FOUND_NICK}'>✅</tg-emoji> Подписка подтверждена!</b>", parse_mode='HTML')
        welcome = (f"<b><tg-emoji emoji-id='{E_HI}'>👋</tg-emoji> Привет.</b>\n\n"
                  f"<b><tg-emoji emoji-id='{E_WELCOME}'>✨</tg-emoji> Ты попал в бота Vertex — username</b>\n\n"
                  f"<b><tg-emoji emoji-id='{E_WHAT}'>💎</tg-emoji> Ты здесь можешь найти:</b>\n"
                  f"<blockquote><b><tg-emoji emoji-id='{E_INFO_LIST}'>▫️</tg-emoji> 5-6 значных юзернеймов.</b>\n"
                  f"<b><tg-emoji emoji-id='{E_INFO_LIST}'>▫️</tg-emoji> Поиск по слову.</b>\n"
                  f"<b><tg-emoji emoji-id='{E_INFO_LIST}'>▫️</tg-emoji> Поиск по фильтру.</b></blockquote>")
        bot.send_message(call.from_user.id, welcome, parse_mode='HTML', reply_markup=get_main_keyboard(call.from_user.id))
    else: bot.answer_callback_query(call.id, "❌ Вы ещё не подписались!", show_alert=True)

REFERRALS_FOR_PREMIUM = 5
REFERRAL_PREMIUM_DAYS = 1

def grant_premium_days(user_id, days):
    """Выдаёт (или продлевает) премиум пользователю на указанное число дней."""
    user = get_user(user_id)
    if not user: return None
    current_expires = user.get('premium_expires')
    if current_expires and user.get('is_premium') == 1:
        try:
            exp_dt = datetime.datetime.strptime(current_expires, '%Y-%m-%d %H:%M:%S').replace(tzinfo=MOSCOW_TZ)
            new_expires = (exp_dt + datetime.timedelta(days=days)) if exp_dt > moscow_now() else (moscow_now() + datetime.timedelta(days=days))
        except:
            new_expires = moscow_now() + datetime.timedelta(days=days)
    else:
        new_expires = moscow_now() + datetime.timedelta(days=days)
    update_user(user_id, is_premium=1, premium_expires=new_expires.strftime('%Y-%m-%d %H:%M:%S'), premium_source='purchase')
    return new_expires

def activate_referral(user_id):
    """Засчитывает реферала. Реферал должен быть подписан на канал (проверяется в вызывающем коде)."""
    user = get_user(user_id)
    if not user or user.get('referral_activated'): return False
    referrer_id = user.get('referrer_id')
    if not referrer_id or referrer_id == user_id: return False
    if not check_channel_subscription(user_id): return False
    with db_lock:
        cursor.execute("UPDATE users SET referrals_count=referrals_count+1 WHERE user_id=?", (referrer_id,))
        cursor.execute("UPDATE users SET referral_activated=1 WHERE user_id=?", (user_id,))
        conn.commit()
        cursor.execute("SELECT referrals_count FROM users WHERE user_id=?", (referrer_id,))
        row = cursor.fetchone()
        ref_count = row[0] if row else 0
    try: bot.send_message(referrer_id, f"<b><tg-emoji emoji-id='{E_REF_TOP}'>🔣</tg-emoji> У Вас новый реферал!</b>\n\n<blockquote><b><tg-emoji emoji-id='{E_REF_COUNT}'>💬</tg-emoji> У Вас рефералов: {ref_count}</b></blockquote>", parse_mode='HTML')
    except: pass
    if ref_count and ref_count % REFERRALS_FOR_PREMIUM == 0:
        new_expires = grant_premium_days(referrer_id, REFERRAL_PREMIUM_DAYS)
        if new_expires:
            try:
                bot.send_message(referrer_id,
                    f"<b><tg-emoji emoji-id='{E_PREMIUM}'>⭐</tg-emoji> Тебе начислен премиум на {REFERRAL_PREMIUM_DAYS} день за {REFERRALS_FOR_PREMIUM} рефералов!</b>\n\n"
                    f"<blockquote>Действует до: {new_expires.strftime('%d.%m.%Y %H:%M')}</blockquote>", parse_mode='HTML')
            except: pass
    return True

_READABLE_VOWELS = 'aeiou'
_READABLE_CONSONANTS = 'bcdfghklmnprstvw'  # без редких букв (q,x,z,j) — не портят score в rate_username

def _generate_readable_nick(length):
    """Генерирует произносимую строку через чередование согласная/гласная (CV-паттерн),
    вместо равномерно случайного набора букв. Даёт высокий alt_ratio и natural_ratio
    в rate_username(), то есть более "читабельные" кандидаты."""
    if length <= 0:
        return ''
    result = []
    next_vowel = random.random() < 0.35  # первая буква иногда гласная, чаще согласная
    for _ in range(length):
        if next_vowel:
            result.append(random.choice(_READABLE_VOWELS))
            next_vowel = random.random() < 0.1   # после гласной почти всегда согласная
        else:
            result.append(random.choice(_READABLE_CONSONANTS))
            next_vowel = random.random() < 0.8   # после согласной почти всегда гласная
    return ''.join(result)

_SEMI_READABLE_POOL = (
    'a'*9+'e'*9+'i'*7+'o'*7+'u'*4          # гласные — с частотным весом
    +'b'*2+'c'*3+'d'*3+'f'*2+'g'*2+'h'*3+'k'*2+'l'*4+'m'*3+'n'*5
    +'p'*2+'r'*5+'s'*5+'t'*6+'v'*2+'w'*1+'y'*2   # согласные — без редких q,x,z,j
)  # используется только для 5 букв в режиме "Читабельный": лёгкий уклон к частым буквам,
   # но без жёсткого чередования согласная/гласная (как в _generate_readable_nick) —
   # иначе для 5 букв почти все "правильные" CV-комбинации уже заняты и поиск станет
   # намного медленнее. Здесь улучшение небольшое, а не кардинальное.

def generate_fast_nick(length=5, mode='random'):
    """mode='readable' — произносимая CV-строка (см. _generate_readable_nick), используется
    для 6-буквенных поисков. mode='semi_readable' — лёгкий уклон к частым буквам без строгого
    чередования, используется для 5-буквенных поисков в режиме "Читабельный" (см. perform_search).
    mode='random' (или любой другой) — полностью случайная строка a-z, равномерно на каждую позицию."""
    if mode == 'readable':
        return _generate_readable_nick(length)
    if mode == 'semi_readable':
        return ''.join(random.choice(_SEMI_READABLE_POOL) for _ in range(length))
    return ''.join(random.choice('abcdefghijklmnopqrstuvwxyz') for _ in range(length))

def _strip_tgemoji(text):
    """Убирает теги <tg-emoji emoji-id='...'>X</tg-emoji>, оставляя только X — запасной
    вариант на случай, если конкретный custom-emoji ID окажется недействительным и
    Telegram целиком отклонит сообщение с ошибкой вроде CUSTOM_EMOJI_INVALID."""
    return re.sub(r"<tg-emoji emoji-id='[^']*'>(.*?)</tg-emoji>", r"\1", text)

def send_html_safe(chat_id, text, reply_markup=None):
    """Отправка HTML-сообщения с фолбэком: если Telegram отклонил сообщение (например,
    из-за недействительного custom-emoji ID), пробуем отправить тот же текст без tg-emoji,
    чтобы функциональность не ломалась молча."""
    try:
        return bot.send_message(chat_id, text, parse_mode='HTML', reply_markup=reply_markup)
    except Exception as e:
        logger.error(f"send_html_safe: ошибка отправки ({e}), пробуем без custom-emoji")
        try:
            return bot.send_message(chat_id, _strip_tgemoji(text), parse_mode='HTML', reply_markup=reply_markup)
        except Exception as e2:
            logger.error(f"send_html_safe: повторная ошибка отправки: {e2}")
            return None

def safe_edit(call, text, markup=None):
    try:
        if markup:
            bot.edit_message_text(text, call.message.chat.id, call.message.message_id, parse_mode='HTML', reply_markup=markup)
        else:
            bot.edit_message_text(text, call.message.chat.id, call.message.message_id, parse_mode='HTML')
    except Exception as e:
        if "message is not modified" not in str(e):
            try:
                bot.edit_message_text(text, call.message.chat.id, call.message.message_id, parse_mode='HTML', reply_markup=markup)
            except Exception as e2:
                logger.error(f"safe_edit: ошибка редактирования ({e2}), пробуем без custom-emoji")
                try:
                    bot.edit_message_text(_strip_tgemoji(text), call.message.chat.id, call.message.message_id, parse_mode='HTML', reply_markup=markup)
                except Exception as e3:
                    logger.error(f"safe_edit: повторная ошибка редактирования: {e3}")

def safe_result_edit(chat_id, msg_id, text, markup=None):
    """Показ результата поиска (найдено/не найдено). Под нагрузкой edit_message_text может
    словить флуд/сетевую ошибку — раньше это молча проглатывалось, и юзер вечно видел
    'Ищу подходящий никнейм...'. Теперь при сбое edit шлём отдельным сообщением, чтобы
    результат дошёл в любом случае."""
    try:
        bot.edit_message_text(text, chat_id, msg_id, parse_mode='HTML', reply_markup=markup)
    except Exception as e:
        if "message is not modified" in str(e):
            return
        logger.warning(f"safe_result_edit: edit не прошёл ({e}), шлём новым сообщением")
        try:
            bot.send_message(chat_id, text, parse_mode='HTML', reply_markup=markup)
        except Exception as e2:
            logger.error(f"safe_result_edit: не удалось отправить результат вообще: {e2}")

def safe_menu_transition(call, text, markup=None):
    """Переход между экранами меню поиска: старое сообщение удаляется и отправляется
    новое текстовое — так переход срабатывает из любого состояния, даже если правка
    на месте почему-то не проходит."""
    chat_id = call.message.chat.id
    try: bot.delete_message(chat_id, call.message.message_id)
    except: pass
    try:
        bot.send_message(chat_id, text, parse_mode='HTML', reply_markup=markup)
    except Exception as e:
        logger.error(f"safe_menu_transition: не удалось отправить: {e}")

def notify_busy(call, text, allow_cancel=False):
    """Сообщает пользователю, что нужно подождать (поиск уже идёт / перегрузка).
    Под нагрузкой callback-запрос может 'протухнуть', пока дошёл до обработки —
    answer_callback_query в этом случае кидает ошибку, и пользователь не видит
    вообще никакого ответа на повторное нажатие. Поэтому при сбое дублируем
    обычным сообщением.
    allow_cancel=True (для reason='already_running') — дополнительно шлём кнопку
    отмены: если предыдущий поиск завис (например, сессии не отвечают), пользователь
    иначе застревает на этом сообщении навсегда, т.к. кнопка отмены есть только на
    сообщении САМОГО поиска, а не на этом предупреждении."""
    try:
        bot.answer_callback_query(call.id, text, show_alert=True)
    except Exception as e:
        logger.warning(f"notify_busy: answer_callback_query не прошёл ({e}), шлём сообщением")
        try: bot.send_message(call.from_user.id, text, parse_mode='HTML')
        except: pass
    if allow_cancel:
        try: bot.send_message(call.from_user.id, "Если поиск завис, можете отменить его:", reply_markup=cancel_markup())
        except: pass

def get_main_keyboard(user_id=None):
    markup = types.ReplyKeyboardMarkup(resize_keyboard=True, row_width=2)
    buttons = [kbtn("Поиск", emoji=E_MAIN, style="primary"), kbtn("Профиль", emoji=E_PROFILE, style="primary"),
               kbtn("Рефералка", emoji=E_REF_TOP, style="primary"), kbtn("Премиум", emoji=E_PREMIUM, style="primary")]
    if WEBAPP_URL:
        buttons.append(kbtn("Открыть приложение", emoji=E_MAIN, web_app=types.WebAppInfo(url=WEBAPP_URL)))
    if user_id == ADMIN_ID: buttons.append(kbtn("Панель управления", emoji=E_ADMIN_MENU, style="primary"))
    markup.add(*buttons)
    return markup

def admin_inline_menu():
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.add(
        btn("Статистика", callback_data="admin_stats", emoji=E_STATS_TITLE, style="primary"),
        btn("Отчёт", callback_data="admin_report", emoji=E_ADMIN_REPORT, style="primary"),
        btn("Сессии", callback_data="admin_sessions", emoji=E_SESSIONS_TITLE, style="primary"),
        btn("Загрузка сессий", callback_data="admin_upload_sessions_zip", emoji=E_SESSION_ADD, style="primary"),
        btn("Бан", callback_data="admin_ban", emoji=E_STATS_BANNED, style="danger"),
        btn("Разбан", callback_data="admin_unban", emoji=E_PROMO_OK, style="success"),
        btn("Рассылка", callback_data="admin_broadcast", emoji=E_BROADCAST, style="primary"),
        btn("Поиск", callback_data="admin_toggle_session_search", emoji=E_MAIN, style="primary"),
        btn("Убрать из топа", callback_data="admin_remove_top_ref", emoji=E_TOP_REF, style="danger"),
        btn("Тех-работы", callback_data="admin_toggle_maintenance", emoji=E_TECH_WORKS, style="danger"),
        btn("Премиум", callback_data="admin_premium", emoji=E_PREMIUM, style="primary"),
        btn("Приёмка", callback_data="admin_priemka", emoji=E_PROMO_STAR, style="primary"),
        btn("Промокоды", callback_data="admin_promo", emoji=E_PROMO_PANEL, style="primary"),
        btn("Юз-пул", callback_data="admin_stock", emoji=E_SESSION_LIST, style="primary")
    )
    return markup

def priemka_status_text():
    status = f"<tg-emoji emoji-id='{E_FOUND_NICK}'>✅</tg-emoji> Включена" if PRIEMKA_ENABLED else f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Выключена"
    acc = f"@{PRIEMKA_USERNAME}" if PRIEMKA_USERNAME else "не задан"
    session_status = "задана" if PRIEMKA_SESSION else "не задана"
    crypto_price = get_crypto_day_price()
    with db_lock:
        cursor.execute("SELECT COUNT(*), COALESCE(SUM(days),0) FROM priemka_transactions WHERE status='credited'")
        cnt, total_days = cursor.fetchone()
        cursor.execute("SELECT COUNT(*), COALESCE(SUM(days),0) FROM crypto_invoices WHERE status='paid'")
        crypto_cnt, crypto_days = cursor.fetchone()
    return (f"<b><tg-emoji emoji-id='{E_PREMIUM}'>🎁</tg-emoji> Приёмка звёзд</b>\n\n"
            f"<blockquote><b>Статус:</b> {status}\n"
            f"<b>Аккаунт:</b> {acc}\n"
            f"<b>Сессия:</b> {session_status}\n"
            f"<b>Цена звёзд:</b> {PRIEMKA_STARS_PER_DAY} <tg-emoji emoji-id='{E_PREMIUM}'>⭐</tg-emoji> = 1 день\n"
            f"<b>Зачислено оплат <tg-emoji emoji-id='{E_PREMIUM}'>⭐</tg-emoji>:</b> {cnt} (всего {total_days} дн.)\n\n"
            f"<b>Цена крипты:</b> {crypto_price}$ = 1 день\n"
            f"<b>Зачислено оплат 💳:</b> {crypto_cnt} (всего {crypto_days} дн.)</blockquote>\n\n"
            f"<i>Отправляйте на этот аккаунт Telegram Stars подарком — бот сам определит отправителя по его Telegram ID (юзернейм не проверяется) и выдаст премиум.</i>")

def priemka_admin_markup():
    markup = types.InlineKeyboardMarkup(row_width=2)
    toggle_label = "Выключить" if PRIEMKA_ENABLED else "Включить"
    markup.add(
        btn("Войти по номеру", callback_data="priemka_set_session", emoji=E_SESSION_ADD_DESC, style="primary"),
        btn("Цена (звёзд/день)", callback_data="priemka_set_price", emoji=E_PROMO_STAR, style="primary"),
        btn("Цена (крипта, $/день)", callback_data="priemka_set_crypto_price", emoji=E_PROMO_STAR2, style="primary"),
        btn(toggle_label, callback_data="priemka_toggle", style="primary"),
        btn("Проверить сейчас", callback_data="priemka_check_now", emoji=E_PROMO_OK, style="success"),
        btn("Последние оплаты", callback_data="priemka_last_tx", emoji=E_HISTORY, style="primary"),
        btn("Назад", callback_data="admin_back", emoji=E_PROMO_BACK, style="primary")
    )
    return markup

@bot.callback_query_handler(func=lambda call: call.data == "admin_priemka")
def admin_priemka_callback(call):
    if call.from_user.id != ADMIN_ID: return
    bot.answer_callback_query(call.id)
    safe_edit(call, priemka_status_text(), priemka_admin_markup())

priemka_temp = {}

@bot.callback_query_handler(func=lambda call: call.data == "priemka_set_session")
def priemka_set_session_callback(call):
    if call.from_user.id != ADMIN_ID: return
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, "Введите номер телефона аккаунта-приёмки (с + или без):\n\nДля отмены напишите «отмена».")
    bot.register_next_step_handler(msg, process_priemka_phone)

def process_priemka_phone(message):
    if message.from_user.id != ADMIN_ID: return
    admin_id = message.from_user.id
    if not message.text: return
    phone = message.text.strip().replace(' ', '').replace('-', '')
    if phone.lower() == 'отмена':
        bot.send_message(admin_id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Отменено", reply_markup=priemka_admin_markup(), parse_mode='HTML'); return
    if not phone.startswith('+'): phone = '+' + phone
    if not phone[1:].isdigit():
        bot.send_message(admin_id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Неверный формат номера", parse_mode='HTML'); return
    msg = bot.send_message(admin_id, f"🔄 Подключаюсь к {phone}...")
    async def connect_and_send():
        client = TelegramClient(StringSession(), API_ID, API_HASH, loop=_async_loop)
        await client.connect()
        await client.send_code_request(phone)
        return client
    try:
        client = run_async(connect_and_send(), timeout=25)
        priemka_temp[admin_id] = {"phone": phone, "client": client}
        bot.edit_message_text(f"<tg-emoji emoji-id='{E_FOUND_NICK}'>✅</tg-emoji> Код отправлен на {phone}\n\n<tg-emoji emoji-id='{E_SESSION_ADD}'>📱</tg-emoji> Введите код:", admin_id, msg.message_id, parse_mode='HTML')
        bot.register_next_step_handler(msg, process_priemka_code)
    except Exception as e:
        bot.edit_message_text(f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Ошибка: {str(e)}", admin_id, msg.message_id, parse_mode='HTML')

def process_priemka_code(message):
    if message.from_user.id != ADMIN_ID: return
    admin_id = message.from_user.id
    if not message.text: return
    code = message.text.strip()
    if code.lower() == 'отмена':
        _priemka_cleanup_temp(admin_id); bot.send_message(admin_id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Отменено", reply_markup=priemka_admin_markup(), parse_mode='HTML'); return
    sd = priemka_temp.get(admin_id)
    if not sd:
        bot.send_message(admin_id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Сессия входа не найдена, начните заново", reply_markup=priemka_admin_markup(), parse_mode='HTML'); return
    client = sd["client"]; phone = sd["phone"]
    msg = bot.send_message(admin_id, "🔄 Проверяю код...")
    async def sign_in(): await client.sign_in(phone, code); return client.session.save()
    try:
        session_string = run_async(sign_in(), timeout=25)
        _priemka_save_session(session_string, admin_id, msg.message_id)
    except errors.SessionPasswordNeededError:
        bot.edit_message_text(f"🔐 <b>Требуется 2FA пароль</b>\n\nВведите облачный пароль от {phone}:", admin_id, msg.message_id, parse_mode='HTML')
        bot.register_next_step_handler(msg, process_priemka_password)
    except errors.PhoneCodeInvalidError:
        bot.edit_message_text(f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> <b>Неверный код</b>\n\nПопробуйте ещё раз:", admin_id, msg.message_id, parse_mode='HTML')
        bot.register_next_step_handler(msg, process_priemka_code)
    except Exception as e:
        bot.edit_message_text(f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Ошибка: {str(e)}", admin_id, msg.message_id, parse_mode='HTML'); _priemka_cleanup_temp(admin_id)

def process_priemka_password(message):
    if message.from_user.id != ADMIN_ID: return
    admin_id = message.from_user.id
    if not message.text: return
    password = message.text.strip()
    if password.lower() == 'отмена':
        _priemka_cleanup_temp(admin_id); bot.send_message(admin_id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Отменено", reply_markup=priemka_admin_markup(), parse_mode='HTML'); return
    sd = priemka_temp.get(admin_id)
    if not sd:
        bot.send_message(admin_id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Сессия входа не найдена, начните заново", reply_markup=priemka_admin_markup(), parse_mode='HTML'); return
    client = sd["client"]
    msg = bot.send_message(admin_id, "🔄 Проверяю пароль...")
    async def sign_in_password(): await client.sign_in(password=password); return client.session.save()
    try:
        session_string = run_async(sign_in_password(), timeout=25)
        _priemka_save_session(session_string, admin_id, msg.message_id)
    except errors.PasswordHashInvalidError:
        bot.edit_message_text(f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> <b>Неверный пароль</b>\n\nПопробуйте ещё раз:", admin_id, msg.message_id, parse_mode='HTML')
        bot.register_next_step_handler(msg, process_priemka_password)
    except Exception as e:
        bot.edit_message_text(f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Ошибка: {str(e)}", admin_id, msg.message_id, parse_mode='HTML'); _priemka_cleanup_temp(admin_id)

def _priemka_save_session(session_string, admin_id, msg_id):
    global PRIEMKA_SESSION, PRIEMKA_USERNAME
    try:
        ok, info = run_async(_priemka_test_session(session_string), timeout=25)
        username = info if ok else None
        save_setting('priemka_session', session_string)
        save_setting('priemka_username', username)
        PRIEMKA_SESSION = session_string
        PRIEMKA_USERNAME = username
        run_async(_priemka_reset_client(), timeout=10)
        label = f"@{username}" if username else "(без юзернейма)"
        bot.edit_message_text(f"<tg-emoji emoji-id='{E_FOUND_NICK}'>✅</tg-emoji> <b>Аккаунт-приёмка подключен!</b>\n\nАккаунт: {label}", admin_id, msg_id, parse_mode='HTML')
        bot.send_message(admin_id, priemka_status_text(), parse_mode='HTML', reply_markup=priemka_admin_markup())
    except Exception as e:
        bot.edit_message_text(f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Ошибка сохранения: {str(e)}", admin_id, msg_id, parse_mode='HTML')
    finally:
        _priemka_cleanup_temp(admin_id)

def _priemka_cleanup_temp(admin_id):
    if admin_id in priemka_temp:
        client = priemka_temp[admin_id].get("client")
        if client:
            try: run_async(client.disconnect())
            except: pass
        del priemka_temp[admin_id]

@bot.callback_query_handler(func=lambda call: call.data == "priemka_set_price")
def priemka_set_price_callback(call):
    if call.from_user.id != ADMIN_ID: return
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, f"Текущая цена: {PRIEMKA_STARS_PER_DAY} <tg-emoji emoji-id='{E_PREMIUM}'>⭐</tg-emoji> = 1 день.\nВведите новое количество звёзд за 1 день премиума:", parse_mode='HTML')
    bot.register_next_step_handler(msg, process_priemka_set_price)

def process_priemka_set_price(message):
    if message.from_user.id != ADMIN_ID: return
    if not message.text: return
    try:
        price = int(message.text.strip())
        if price <= 0: raise ValueError
    except ValueError:
        bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Введите число больше 0!", reply_markup=priemka_admin_markup(), parse_mode='HTML'); return
    global PRIEMKA_STARS_PER_DAY
    PRIEMKA_STARS_PER_DAY = price
    save_setting('priemka_stars_per_day', price)
    bot.send_message(message.chat.id, priemka_status_text(), parse_mode='HTML', reply_markup=priemka_admin_markup())

@bot.callback_query_handler(func=lambda call: call.data == "priemka_set_crypto_price")
def priemka_set_crypto_price_callback(call):
    if call.from_user.id != ADMIN_ID: return
    bot.answer_callback_query(call.id)
    msg = bot.send_message(call.message.chat.id, f"Текущая цена: {get_crypto_day_price()}$ = 1 день.\nВведите новую цену в $ за 1 день премиума (например 0.35):")
    bot.register_next_step_handler(msg, process_priemka_set_crypto_price)

def process_priemka_set_crypto_price(message):
    if message.from_user.id != ADMIN_ID: return
    if not message.text: return
    try:
        price = float(message.text.strip().replace(',', '.'))
        if price <= 0: raise ValueError
    except ValueError:
        bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Введите число больше 0!", reply_markup=priemka_admin_markup(), parse_mode='HTML'); return
    save_setting('crypto_day_price_usd', price)
    bot.send_message(message.chat.id, priemka_status_text(), parse_mode='HTML', reply_markup=priemka_admin_markup())

@bot.callback_query_handler(func=lambda call: call.data == "priemka_toggle")
def priemka_toggle_callback(call):
    if call.from_user.id != ADMIN_ID: return
    global PRIEMKA_ENABLED
    if not PRIEMKA_SESSION:
        bot.answer_callback_query(call.id, "❌ Сначала задайте сессию!", show_alert=True); return
    PRIEMKA_ENABLED = not PRIEMKA_ENABLED
    save_setting('priemka_enabled', '1' if PRIEMKA_ENABLED else '0')
    bot.answer_callback_query(call.id, "Включено" if PRIEMKA_ENABLED else "Выключено")
    safe_edit(call, priemka_status_text(), priemka_admin_markup())

@bot.callback_query_handler(func=lambda call: call.data == "priemka_check_now")
def priemka_check_now_callback(call):
    if call.from_user.id != ADMIN_ID: return
    if not PRIEMKA_SESSION:
        bot.answer_callback_query(call.id, "❌ Сначала задайте сессию!", show_alert=True); return
    bot.answer_callback_query(call.id, "Проверяю...")
    def _run():
        try: process_priemka_transactions()
        except Exception as e: logger.error(f"priemka_check_now: {e}")
        try: bot.send_message(call.message.chat.id, f"<tg-emoji emoji-id='{E_FOUND_NICK}'>✅</tg-emoji> Проверка завершена", reply_markup=priemka_admin_markup(), parse_mode='HTML')
        except: pass
    threading.Thread(target=_run, daemon=True).start()

@bot.callback_query_handler(func=lambda call: call.data == "priemka_last_tx")
def priemka_last_tx_callback(call):
    if call.from_user.id != ADMIN_ID: return
    bot.answer_callback_query(call.id)
    with db_lock:
        cursor.execute("SELECT sender_id, stars, days, status, created_at FROM priemka_transactions ORDER BY created_at DESC LIMIT 15")
        rows = cursor.fetchall()
    if not rows:
        text = "Транзакций пока нет."
    else:
        lines = []
        for sender_id, stars, days, status, created_at in rows:
            lines.append(f"{created_at} — ID {sender_id} — {stars}<tg-emoji emoji-id='{E_PREMIUM}'>⭐</tg-emoji> — {days}д — {status}")
        text = "<b>Последние транзакции:</b>\n\n" + "\n".join(lines)
    bot.send_message(call.message.chat.id, text, reply_markup=priemka_admin_markup())

@bot.message_handler(commands=['start'])
def start(message):
    user_id = message.from_user.id
    if MAINTENANCE_MODE and user_id != ADMIN_ID:
        bot.send_message(user_id, f"<b><tg-emoji emoji-id='{E_TECH_WORKS_TITLE}'>🔧</tg-emoji> Использование бота невозможно.</b>\n\n<blockquote><b><tg-emoji emoji-id='{E_TECH_WORKS}'>🛠</tg-emoji> Проводяться технические работы.</b></blockquote>", parse_mode='HTML')
        return
    if is_banned(user_id):
        bot.send_message(user_id, f"<b><tg-emoji emoji-id='{E_BANNED}'>🚫</tg-emoji> Извините, но вы заблокированы.</b>\n\n<blockquote><b><tg-emoji emoji-id='{E_BANNED_REASON}'>📝</tg-emoji> Можете написать владельцу @nuemc, объяснить ситуацию, и попросить разбанить</b></blockquote>", parse_mode='HTML')
        return
    username = message.from_user.username
    referrer_id = None
    if len(message.text.split()) > 1:
        try: referrer_id = int(message.text.split()[1])
        except: pass
    user, is_new = create_user(user_id, username, referrer_id)
    user_last_action[user_id] = time.time()
    if check_subscription(user_id):
        activate_referral(user_id)
        welcome = (f"<b><tg-emoji emoji-id='{E_HI}'>👋</tg-emoji> Привет.</b>\n\n"
                  f"<b><tg-emoji emoji-id='{E_WELCOME}'>✨</tg-emoji> Ты попал в бота Vertex — username</b>\n\n"
                  f"<b><tg-emoji emoji-id='{E_WHAT}'>💎</tg-emoji> Ты здесь можешь найти:</b>\n"
                  f"<blockquote><b><tg-emoji emoji-id='{E_INFO_LIST}'>▫️</tg-emoji> 5-6 значных юзернеймов.</b>\n"
                  f"<b><tg-emoji emoji-id='{E_INFO_LIST}'>▫️</tg-emoji> Поиск по слову.</b>\n"
                  f"<b><tg-emoji emoji-id='{E_INFO_LIST}'>▫️</tg-emoji> Поиск по фильтру.</b></blockquote>")
        bot.send_message(user_id, welcome, parse_mode='HTML', reply_markup=get_main_keyboard(user_id))
    else:
        text = (f"<b><tg-emoji emoji-id='{E_ACCESS_DENIED}'>🔒</tg-emoji> Доступ к боту ограничен.</b>\n\n"
                f"<blockquote><b><tg-emoji emoji-id='{E_ACCESS_CHANNEL}'>📢</tg-emoji> Чтобы использовать бота нужно подписаться на канал. затем нажать на кнопку проверки.</b></blockquote>")
        markup = types.InlineKeyboardMarkup(row_width=1)
        markup.add(btn("Подписаться", url=CHANNEL_LINK, emoji=E_CHANNEL_LABEL, style="primary"), btn("Проверить", callback_data="check_sub", emoji=E_PROMO_OK, style="success"))
        bot.send_message(user_id, text, parse_mode='HTML', reply_markup=markup)

@bot.message_handler(func=lambda m: m.text == "Поиск")
@subscription_required
def search_menu_handler(message):
    user_id = message.from_user.id
    user_last_action[user_id] = time.time()
    text = (f"<b><tg-emoji emoji-id='{E_WARN}'>🔍</tg-emoji> Ты открыл меню поиска.</b>\n\n"
            f"<blockquote><b><tg-emoji emoji-id='{E_PLANE}'>🚀</tg-emoji> Твой будущий юзернейм уже ждёт тебя.</b>\n"
            f"<b><tg-emoji emoji-id='{E_CHOOSE_WAY}'>🎯</tg-emoji> Осталось выбрать способ найти его.</b></blockquote>\n\n"
            f"<b><tg-emoji emoji-id='{E_CHOOSE}'>📂</tg-emoji> Выбери раздел:</b>")
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.add(btn("Настройки", callback_data="search_settings", emoji=E_SETTINGS, style="primary"))
    markup.add(btn("5 букв", callback_data="search_len_5", emoji=E_LETTERS, style="primary"),
               btn("6 букв", callback_data="search_len_6", emoji=E_LETTERS, style="primary"),
               btn("Фильтр", callback_data="search_mode_filter", emoji=E_CHOOSE_WAY, style="primary"),
               btn("Слово", callback_data="search_mode_word", emoji=E_CHOOSE_WAY, style="primary"),
               btn("Ловушка", callback_data="search_trap", emoji=E_TRAP_TITLE, style="primary"),
               btn("Закрыть", callback_data="search_close", emoji=E_WARN, style="danger"))
    bot.send_message(user_id, text, parse_mode='HTML', reply_markup=markup)

@bot.callback_query_handler(func=lambda call: call.data == "search_close")
def search_close_handler(call):
    bot.answer_callback_query(call.id)
    bot.delete_message(call.message.chat.id, call.message.message_id)

@bot.callback_query_handler(func=lambda call: call.data == "search_back_to_menu")
def search_back_to_menu(call):
    user_id = call.from_user.id
    bot.answer_callback_query(call.id)
    text = (f"<b><tg-emoji emoji-id='{E_WARN}'>🔍</tg-emoji> Ты открыл меню поиска.</b>\n\n"
            f"<blockquote><b><tg-emoji emoji-id='{E_PLANE}'>🚀</tg-emoji> Твой будущий юзернейм уже ждёт тебя.</b>\n"
            f"<b><tg-emoji emoji-id='{E_CHOOSE_WAY}'>🎯</tg-emoji> Осталось выбрать способ найти его.</b></blockquote>\n\n"
            f"<b><tg-emoji emoji-id='{E_CHOOSE}'>📂</tg-emoji> Выбери раздел:</b>")
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.add(btn("Настройки", callback_data="search_settings", emoji=E_SETTINGS, style="primary"))
    markup.add(btn("5 букв", callback_data="search_len_5", emoji=E_LETTERS, style="primary"),
               btn("6 букв", callback_data="search_len_6", emoji=E_LETTERS, style="primary"),
               btn("Фильтр", callback_data="search_mode_filter", emoji=E_CHOOSE_WAY, style="primary"),
               btn("Слово", callback_data="search_mode_word", emoji=E_CHOOSE_WAY, style="primary"),
               btn("Ловушка", callback_data="search_trap", emoji=E_TRAP_TITLE, style="primary"),
               btn("Закрыть", callback_data="search_close", emoji=E_WARN, style="danger"))
    safe_menu_transition(call, text, markup)

@bot.callback_query_handler(func=lambda call: call.data == "search_settings")
def search_settings_handler(call):
    user_id = call.from_user.id; bot.answer_callback_query(call.id)
    current_mode = get_user_search_mode(user_id)
    mode_text = 'Читабельный' if current_mode == 'readable' else 'Рандомный'
    text = (f"<b><tg-emoji emoji-id='{E_SETTINGS}'>⚙️</tg-emoji> Настройки находки юзернейма.</b>\n\n"
            f"<b><tg-emoji emoji-id='{E_SETTINGS_MODE}'>📋</tg-emoji> Включен режим: {mode_text}</b>\n\n"
            f"<b>В чём разница?</b>\n"
            f"<blockquote><b><tg-emoji emoji-id='{E_SETTINGS_READABLE}'>✅</tg-emoji> Читабельный - данный режим помогает находить читаемые никнеймы.</b>\n"
            f"<b><tg-emoji emoji-id='{E_SETTINGS_READABLE}'>✅</tg-emoji> Рандом - данный режим помогает находить рандомные никнеймы.</b></blockquote>\n\n"
            f"<b><tg-emoji emoji-id='{E_SETTINGS_HINT}'>💡</tg-emoji> Чтобы сменить режим нажми на кнопку ниже</b>")
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.add(btn("Читабельный", callback_data="search_mode_readable", emoji=E_SETTINGS_READABLE, style="primary"),
               btn("Рандомный", callback_data="search_mode_random", emoji=E_CHOOSE, style="primary"),
               btn("Назад", callback_data="search_back_to_menu", emoji=E_PROMO_BACK, style="primary"))
    safe_menu_transition(call, text, markup)

@bot.callback_query_handler(func=lambda call: call.data in ["search_mode_readable", "search_mode_random"])
def search_mode_set(call):
    user_id = call.from_user.id
    mode = 'readable' if call.data == "search_mode_readable" else 'random'
    set_user_search_mode(user_id, mode)
    bot.answer_callback_query(call.id, f"Режим: {'Читабельный' if mode == 'readable' else 'Рандомный'}")
    search_settings_handler(call)

@bot.callback_query_handler(func=lambda call: call.data in ["search_len_5","search_len_6"])
@subscription_required
def search_len_handler(call):
    user_id = call.from_user.id; length = 5 if call.data == "search_len_5" else 6
    bot.answer_callback_query(call.id)
    text = f"<b><tg-emoji emoji-id='{E_MAIN}'>📝</tg-emoji> {length} букв</b>\n\n<b><tg-emoji emoji-id='{E_CHOOSE}'>📂</tg-emoji> Выбери:</b>"
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.add(btn("С цифрами", callback_data=f"search_start_{length}_digits", emoji=E_CHOOSE, style="primary"),
               btn("Без цифр", callback_data=f"search_start_{length}_nodigits", emoji=E_CHOOSE, style="primary"),
               btn("Назад", callback_data="search_back_to_menu", emoji=E_PROMO_BACK, style="primary"))
    safe_menu_transition(call, text, markup)

@bot.callback_query_handler(func=lambda call: call.data.startswith("search_start_"))
@subscription_required
def search_start_handler(call):
    parts = call.data.split("_"); length = int(parts[2]); mode = parts[3]
    user_id = call.from_user.id
    if not can_search(user_id):
        bot.answer_callback_query(call.id, f"Бесплатные поиски закончились ({FREE_DAILY_SEARCHES}/день). Оформи премиум в разделе «Премиум».", show_alert=True)
        return
    ok, reason = try_start_check(user_id)
    if not ok:
        notify_busy(call, OVERLOAD_TEXT if reason == 'overload' else BUSY_CHECK_TEXT, allow_cancel=(reason == 'already_running'))
        return
    bot.answer_callback_query(call.id)

    _hard_ev = start_hard_release_watchdog(user_id, user_id)
    def _run():
        try:
            perform_search(user_id, length, call.message, mode)
        finally:
            _hard_ev.set()
            end_check(user_id)
    threading.Thread(target=_run, daemon=True).start()

SEARCH_TIME_BUDGET = 30
PROGRESS_UPDATE_EVERY = 0.7

# Общий пул потоков для параллельной проверки кандидатов внутри ОДНОГО поиска.
# Раньше run_candidate_search принимала параметр workers, но никогда его не
# использовала — кандидаты проверялись строго по одному (обычный for-цикл).
# Одна проверка (HTTP + сессия) может занимать до ~45с при занятом пуле сессий
# (до 3 попыток по 15с внутри verify_with_session), а на весь поиск отведено
# всего SEARCH_TIME_BUDGET=30с — то есть однопоточно почти никогда не успевали
# дойти даже до второго кандидата, и поиск заканчивался неудачей, хотя другие
# кандидаты в это же самое время оказывались свободны (это видно в логах:
# сессии подтверждают "free", а конкретный поиск их даже не пробовал).
# Размер пула — с запасом под MAX_CONCURRENT_SEARCHES одновременных поисков,
# каждый из которых может держать в полёте до CHECK_WORKERS задач.
_candidate_check_pool = ThreadPoolExecutor(max_workers=600, thread_name_prefix='candchk')

def _run_on_result_safe(fut, on_result):
    try:
        res = fut.result()
    except Exception:
        res = None
    if res:
        try: on_result(res)
        except Exception: pass

def run_candidate_search(chat_id, msg_id, tasks, workers, cancel_event=None, on_result=None):
    """on_result (если передан) вызывается для КАЖДОГО кандидата, который прошёл проверку
    как free — включая те, что доехали до результата уже после того, как поиск отдал
    пользователю первый найденный ник (они всё равно доработают в фоне, т.к. мы их не
    дожидаемся — см. комментарий ниже). Так лишние подтверждённые сессией ники не
    теряются, а попадают, например, в пул (см. stock_add)."""
    checked = 0
    checked_lock = threading.Lock()
    found = None
    cancelled = False
    start = time.time()
    task_iter = iter(tasks)
    in_flight = set()

    def submit_next():
        try:
            t = next(task_iter)
        except StopIteration:
            return None
        fut = _candidate_check_pool.submit(t)
        if on_result is not None:
            fut.add_done_callback(lambda f: _run_on_result_safe(f, on_result))
        return fut

    # Строго последовательно: следующий кандидат уходит на проверку только после
    # того, как предыдущий вернул чёткий результат (и не оказался свободен).
    # Параметр workers сохранён для совместимости сигнатуры, но конкурентность
    # внутри одного поиска больше не используется (раньше было до 3 параллельно).
    initial_workers = 1
    for _ in range(initial_workers):
        fut = submit_next()
        if fut is not None:
            in_flight.add(fut)

    while in_flight:
        if cancel_event is not None and cancel_event.is_set():
            cancelled = True
            break
        if time.time() - start >= SEARCH_TIME_BUDGET:
            break
        done, in_flight = wait(in_flight, timeout=0.3, return_when=FIRST_COMPLETED)
        for fut in done:
            try:
                res = fut.result()
            except Exception:
                res = None
            with checked_lock:
                checked += 1
            if res:
                found = res
                break
            nf = submit_next()
            if nf is not None:
                in_flight.add(nf)
        if found:
            break
    # Незавершённые задачи (если есть) сознательно не дожидаемся — общий пул
    # доработает их в фоне сам, чтобы не задерживать ответ пользователю.
    return found, checked, cancelled

# ============================================================================
# --- Чистое ядро поиска (без Telegram-UI) ---
# Используется и ботом (через тонкие UI-обёртки ниже), и веб-API (/api/search).
# Всегда сами проверяют cooldown/can_search — вызывающая сторона (бот или API)
# может дополнительно проверить их раньше только чтобы показать УДОБНЫЙ текст,
# но именно эти функции — источник истины.
# ============================================================================

def find_username(user_id, length, mode="nodigits", cancel_event=None, pretaken_username=None):
    """Ищет свободный юзернейм заданной длины/режима.
    pretaken_username — если вызывающий уже сам взял ник из пула (stock_take) и
    просто хочет провести его через запись/рейтинг, не запуская повторный поиск.
    Возвращает dict:
      {'status': 'cooldown', 'seconds': N}
      {'status': 'no_search_left'}
      {'status': 'found', 'username': str, 'rating': int, 'length': int}
      {'status': 'not_found'}
      {'status': 'cancelled'}
    """
    cd = get_search_cooldown_remaining(user_id)
    if cd > 0:
        return {'status': 'cooldown', 'seconds': int(cd) + 1}
    if not can_search(user_id):
        return {'status': 'no_search_left'}
    user = get_user(user_id)
    if not user: user, _ = create_user(user_id)
    smode = get_user_search_mode(user_id)
    # Полный CV-паттерн (readable) для 5 букв не используем — почти все "правильные"
    # комбинации такой длины уже заняты, поиск станет слишком медленным. Но и полностью
    # игнорировать выбор пользователя не стоит — если он выбрал "Читабельный", даём лёгкий
    # уклон к частым буквам (semi_readable) вместо жёсткого random. Для остальных длин,
    # кроме 6, читабельность не имеет смысла — там всегда чистый random.
    if length == 5:
        smode = 'semi_readable' if smode == 'readable' else 'random'
    elif length != 6:
        smode = 'random'

    if pretaken_username:
        username = pretaken_username
    else:
        # Сначала смотрим пул "лишних" ников (см. stock_add) — если там уже лежит подходящий
        # по длине/режиму ник, отдаём его сразу, вообще не трогая сессии.
        stocked = stock_take(length, mode)
        if stocked:
            username = stocked
        else:
            def gen_candidate():
                if mode == "digits":
                    digits_count = random.randint(1, 2); letters_count = length - digits_count
                    if letters_count < 1: letters_count = 1; digits_count = length - letters_count
                    cand = generate_fast_nick(letters_count, smode)
                    for _ in range(digits_count):
                        pos = random.randint(1, len(cand))
                        cand = cand[:pos] + str(random.randint(0, 9)) + cand[pos:]
                    return cand[:length]
                return generate_fast_nick(length, smode)

            verify_budget = SessionVerifyBudget()
            def try_candidate():
                cand = gen_candidate()
                if cand[0].isdigit() or len(cand) != length:
                    return None
                if not passes_checks(user_id, cand, verify_budget):
                    return None
                return cand

            # Пока идёт поиск, параллельно могут подтвердиться free сразу НЕСКОЛЬКО кандидатов
            # (несколько сессий одновременно) — заберём в поиск только первый, а остальные,
            # чтобы не тратить проверку впустую, складываем в пул на будущее.
            def _stash_extra(cand):
                stock_add(cand, length, mode)

            tasks = [try_candidate for _ in range(SEARCH_ATTEMPTS)]
            username, checked, cancelled = run_candidate_search(user_id, None, tasks, 1, cancel_event, on_result=_stash_extra)
            if not username:
                return {'status': 'cancelled' if cancelled else 'not_found'}
            # Этот ник уже уходит пользователю напрямую — не должен также лежать в пуле
            # (мог попасть туда через _stash_extra как раз параллельно с этим же результатом).
            stock_remove(username)

    rating = record_found_username(user_id, username, length, user)
    user_last_action[user_id] = time.time()
    return {'status': 'found', 'username': username, 'rating': rating, 'length': length}


def find_by_filter(user_id, mask_input, cancel_event=None):
    """Ищет юзернейм по маске (буквы + '?' как случайная буква). Та же логика
    проверок, что была в process_filter, но без Telegram-UI."""
    cd = get_search_cooldown_remaining(user_id)
    if cd > 0:
        return {'status': 'cooldown', 'seconds': int(cd) + 1}
    if not can_search(user_id):
        return {'status': 'no_search_left'}
    mask_input = (mask_input or '').strip().lower()
    if not mask_input or len(mask_input) < 5 or len(mask_input) > 15:
        return {'status': 'error', 'message': 'Маска должна быть от 5 до 15 символов'}
    if not all(c == '?' or c in 'abcdefghijklmnopqrstuvwxyz' for c in mask_input):
        return {'status': 'error', 'message': 'Разрешены только английские буквы и знак ?'}
    user = get_user(user_id)
    if not user: user, _ = create_user(user_id)

    verify_budget = SessionVerifyBudget()
    def gen_and_check():
        username = "".join(random.choice('abcdefghijklmnopqrstuvwxyz') if ch == '?' else ch for ch in mask_input if ch == '?' or ch.isalpha())
        if len(username) < 5 or len(username) > 32: return None
        if not passes_checks(user_id, username, verify_budget):
            return None
        return username

    tasks = [gen_and_check for _ in range(FILTER_ATTEMPTS)]
    username, checked, cancelled = run_candidate_search(user_id, None, tasks, 1, cancel_event)
    if not username:
        return {'status': 'cancelled' if cancelled else 'not_found'}
    rating = record_found_username(user_id, username, len(username), user)
    user_last_action[user_id] = time.time()
    return {'status': 'found', 'username': username, 'rating': rating, 'length': len(username)}


def find_by_word(user_id, word, word_type="random", cancel_event=None):
    """Ищет юзернейм с заданным словом (префикс/суффикс/оба). Та же логика
    проверок, что была в process_word, но без Telegram-UI."""
    cd = get_search_cooldown_remaining(user_id)
    if cd > 0:
        return {'status': 'cooldown', 'seconds': int(cd) + 1}
    if not can_search(user_id):
        return {'status': 'no_search_left'}
    word = (word or '').strip().lower()
    if len(word) < 3 or len(word) > 10 or not all(c in 'abcdefghijklmnopqrstuvwxyz' for c in word):
        return {'status': 'error', 'message': 'Слово должно быть 3-10 английских букв'}
    user = get_user(user_id)
    if not user: user, _ = create_user(user_id)

    if word_type == "prefix": combos = [(p, word) for p in prefixes]
    elif word_type == "suffix": combos = [(word, s) for s in suffixes]
    else: combos = [(p, word) for p in prefixes] + [(word, s) for s in suffixes]
    random.shuffle(combos)
    candidates = combos[:SEARCH_ATTEMPTS]

    verify_budget = SessionVerifyBudget()
    def check_combo(pair):
        prefix, suffix = pair
        cand = prefix + suffix
        if len(cand) < 5 or len(cand) > 32: return None
        if not passes_checks(user_id, cand, verify_budget):
            return None
        return cand

    tasks = [(lambda pair=pair: check_combo(pair)) for pair in candidates]
    username, checked, cancelled = run_candidate_search(user_id, None, tasks, 1, cancel_event)
    if not username:
        return {'status': 'cancelled' if cancelled else 'not_found'}
    rating = record_found_username(user_id, username, len(username), user)
    user_last_action[user_id] = time.time()
    return {'status': 'found', 'username': username, 'rating': rating, 'length': len(username)}


# ============================================================================
# --- UI-обёртка бота поверх find_username: только рисует сообщения/клавиатуры,
# вся логика поиска — в find_username выше. ---
# ============================================================================

def perform_search(user_id, length, msg_to_edit=None, mode="nodigits"):
    cd = get_search_cooldown_remaining(user_id)
    if cd > 0:
        cd_markup = types.InlineKeyboardMarkup(row_width=1)
        cd_markup.add(btn("Попробовать ещё", callback_data=f"search_start_{length}_{mode}", emoji=E_PROMO_SEARCH, style="primary"))
        try: bot.edit_message_text(f"<b><tg-emoji emoji-id='{E_MAIN}'>⏳</tg-emoji> Подожди {int(cd)+1} сек. перед новым поиском.</b>", user_id, msg_to_edit.message_id, parse_mode='HTML', reply_markup=cd_markup)
        except: pass
        return
    if not can_search(user_id):
        try: bot.edit_message_text(no_search_left_text(user_id), user_id, msg_to_edit.message_id, parse_mode='HTML', reply_markup=premium_upsell_markup())
        except: pass
        return

    # Смотрим пул "лишних" ников здесь же (а не внутри find_username), чтобы решить,
    # нужно ли вообще показывать "Ищу подходящий никнейм..." — если ник уже в пуле,
    # ответ мгновенный и отдельное сообщение не нужно, как и раньше.
    stocked = stock_take(length, mode)
    cancel_ev = None
    if not stocked:
        search_caption = f"<b><tg-emoji emoji-id='{E_MAIN}'>⏰</tg-emoji> Ищу подходящий никнейм...</b>"
        try: bot.delete_message(user_id, msg_to_edit.message_id)
        except: pass
        msg_to_edit = bot.send_message(user_id, search_caption, parse_mode='HTML', reply_markup=cancel_markup())
        cancel_ev = register_search(user_id, user_id, msg_to_edit.message_id)

    result = find_username(user_id, length, mode, cancel_event=cancel_ev, pretaken_username=stocked)
    if cancel_ev is not None:
        unregister_search(user_id, cancel_ev)

    if result['status'] in ('cooldown', 'no_search_left'):
        # Не должно происходить (проверили выше), но на всякий случай не оставляем
        # пользователя с "Ищу..." навсегда.
        try: bot.edit_message_text(no_search_left_text(user_id) if result['status'] == 'no_search_left' else "<b>⏳ Подожди немного и попробуй снова.</b>", user_id, msg_to_edit.message_id, parse_mode='HTML')
        except: pass
        return

    if result['status'] != 'found':
        fail_markup = types.InlineKeyboardMarkup(row_width=2)
        fail_markup.add(btn("Попробовать ещё раз", callback_data=f"search_start_{length}_{mode}", emoji=E_PROMO_SEARCH, style="primary"),
                         btn("Назад", callback_data="search_back_to_menu", emoji=E_PROMO_BACK, style="primary"))
        fail_text = (f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Поиск отменён.</b>" if result['status'] == 'cancelled'
                     else f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Не удалось найти свободный ник. Попробуйте ещё раз.</b>")
        safe_result_edit(user_id, msg_to_edit.message_id, fail_text, fail_markup)
        return

    username, rating = result['username'], result['rating']
    win_text = (f"<b><tg-emoji emoji-id='{E_FOUND_NICK}'>✅</tg-emoji> Юзернейм найден.</b>\n\n"
               f"<blockquote><b><tg-emoji emoji-id='{E_NICK_LABEL}'>📛</tg-emoji> Юзернейм:</b> @{username}\n"
               f"<b><tg-emoji emoji-id='{E_CLICKABLE}'>🔗</tg-emoji> Кликабельно:</b> <code>{username}</code>\n"
               f"<b><tg-emoji emoji-id='{E_LETTERS}'>📏</tg-emoji> Кол-во символов:</b> {length}</blockquote>\n\n"
               f"<b><tg-emoji emoji-id='{E_RATING}'>⭐</tg-emoji> Оценка юзернейма: {rating}/10</b>\n\n"
               f"<b><tg-emoji emoji-id='{E_CHANNEL_LABEL}'>📢</tg-emoji> Наш канал:</b> {REQUIRED_CHANNEL}")
    sm = types.InlineKeyboardMarkup(row_width=2)
    sm.add(btn("Найти ещё", callback_data=f"search_start_{length}_{mode}", emoji=E_FOUND_NICK, style="success"),
           btn("Назад", callback_data="search_back_to_menu", emoji=E_PROMO_BACK, style="primary"))
    safe_result_edit(user_id, msg_to_edit.message_id, win_text, sm)
    return

@bot.callback_query_handler(func=lambda call: call.data == "search_mode_filter")
@subscription_required
def filter_menu_handler(call):
    user_id = call.from_user.id; bot.answer_callback_query(call.id)
    text = (f"<b><tg-emoji emoji-id='{E_CHOOSE}'>🪧</tg-emoji> Фильтр</b>\n\n"
            f"<b><tg-emoji emoji-id='{E_MAIN}'>🤔</tg-emoji> Как работает?</b>\n"
            f"<blockquote><b><tg-emoji emoji-id='{E_INFO_LIST}'>📝</tg-emoji> Вы вводите слово от 5-15 символов (только английские). Знак <code>?</code>, это любая случайная буква. И получаете никнейм.</b></blockquote>\n\n"
            f"<b><tg-emoji emoji-id='{E_PLANE}'>📌</tg-emoji> Например:</b> <code>oer????wer</code>")
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.add(btn("Ввести", callback_data="filter_input", emoji=E_CLICKABLE, style="primary"), btn("Назад", callback_data="search_back_to_menu", emoji=E_PROMO_BACK, style="primary"))
    bot.clear_step_handler_by_chat_id(user_id)
    bot.send_message(user_id, text, parse_mode='HTML', reply_markup=markup)

@bot.callback_query_handler(func=lambda call: call.data == "filter_input")
def filter_input_callback(call):
    user_id = call.from_user.id; bot.answer_callback_query(call.id)
    if not can_search(user_id):
        bot.answer_callback_query(call.id, f"Бесплатные поиски закончились ({FREE_DAILY_SEARCHES}/день). Оформи премиум в разделе «Премиум».", show_alert=True)
        return
    bot.clear_step_handler_by_chat_id(user_id)
    msg = bot.send_message(user_id, f"<b><tg-emoji emoji-id='{E_MAIN}'>📝</tg-emoji> Введите маску для фильтра:</b>", parse_mode='HTML')
    bot.register_next_step_handler(msg, process_filter_guarded, msg)

def process_filter_guarded(message, original_msg=None):
    user_id = message.from_user.id
    ok, reason = try_start_check(user_id)
    if not ok:
        bot.send_message(user_id, OVERLOAD_TEXT if reason == 'overload' else BUSY_CHECK_TEXT, parse_mode='HTML',
                         reply_markup=(cancel_markup() if reason == 'already_running' else None))
        return
    _hard_ev = start_hard_release_watchdog(user_id, user_id)
    def _run():
        try:
            process_filter(message, original_msg)
        finally:
            _hard_ev.set()
            end_check(user_id)
    threading.Thread(target=_run, daemon=True).start()

def process_filter(message, original_msg=None):
    user_id = message.from_user.id
    if not message.text: bot.send_message(user_id, f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Отправьте текст!</b>", parse_mode='HTML'); return
    cd = get_search_cooldown_remaining(user_id)
    if cd > 0:
        mask_for_retry = message.text.strip().lower()
        cd_markup = types.InlineKeyboardMarkup(row_width=1)
        cd_markup.add(btn("Попробовать ещё", callback_data=f"filter_again_{mask_for_retry}", emoji=E_PROMO_SEARCH, style="primary"))
        bot.send_message(user_id, f"<b><tg-emoji emoji-id='{E_MAIN}'>⏳</tg-emoji> Подожди {int(cd)+1} сек. перед новым поиском.</b>", parse_mode='HTML', reply_markup=cd_markup); return
    if not can_search(user_id):
        bot.send_message(user_id, no_search_left_text(user_id), parse_mode='HTML', reply_markup=premium_upsell_markup()); return
    mask_input = message.text.strip().lower()
    if not mask_input or len(mask_input) < 5 or len(mask_input) > 15:
        bot.send_message(user_id, f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Маска должна быть от 5 до 15 символов!</b>", parse_mode='HTML'); return
    if not all(c == '?' or c in 'abcdefghijklmnopqrstuvwxyz' for c in mask_input):
        bot.send_message(user_id, f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Разрешены только английские буквы и знак ?</b>", parse_mode='HTML'); return
    user = get_user(user_id)
    if not user: user, _ = create_user(user_id)
    search_caption = f"<b><tg-emoji emoji-id='{E_MAIN}'>⏰</tg-emoji> Ищу подходящий никнейм...</b>"
    if original_msg:
        try: bot.delete_message(user_id, original_msg.message_id)
        except: pass
    original_msg = bot.send_message(user_id, search_caption, parse_mode='HTML', reply_markup=cancel_markup())
    cancel_ev = register_search(user_id, user_id, original_msg.message_id)

    verify_budget = SessionVerifyBudget()
    def gen_and_check():
        username = "".join(random.choice('abcdefghijklmnopqrstuvwxyz') if ch == '?' else ch for ch in mask_input if ch == '?' or ch.isalpha())
        if len(username) < 5 or len(username) > 32: return None
        if not passes_checks(user_id, username, verify_budget):
            return None
        return username

    workers = 1
    tasks = [gen_and_check for _ in range(FILTER_ATTEMPTS)]
    username, checked, cancelled = run_candidate_search(user_id, original_msg.message_id, tasks, workers, cancel_ev)
    unregister_search(user_id, cancel_ev)

    if username:
        rating = record_found_username(user_id, username, len(username), user)
        user_last_action[user_id] = time.time()
        win_text = (f"<b><tg-emoji emoji-id='{E_FOUND_NICK}'>✅</tg-emoji> Юзернейм найден.</b>\n\n"
                   f"<blockquote><b><tg-emoji emoji-id='{E_NICK_LABEL}'>📛</tg-emoji> Юзернейм:</b> @{username}\n"
                   f"<b><tg-emoji emoji-id='{E_CLICKABLE}'>🔗</tg-emoji> Кликабельно:</b> <code>{username}</code>\n"
                   f"<b><tg-emoji emoji-id='{E_LETTERS}'>📏</tg-emoji> Кол-во букв:</b> {len(username)}</blockquote>\n\n"
                   f"<b><tg-emoji emoji-id='{E_RATING}'>⭐</tg-emoji> Оценка юзернейма: {rating}/10</b>\n\n"
                   f"<b><tg-emoji emoji-id='{E_CHANNEL_LABEL}'>📢</tg-emoji> Наш канал:</b> {REQUIRED_CHANNEL}")
        fm = types.InlineKeyboardMarkup(row_width=2)
        fm.add(btn("Найти ещё", callback_data=f"filter_again_{mask_input}", emoji=E_FOUND_NICK, style="success"), btn("Назад", callback_data="search_back_to_menu", emoji=E_PROMO_BACK, style="primary"))
        safe_result_edit(user_id, original_msg.message_id, win_text, fm)
        return
    fail_markup = types.InlineKeyboardMarkup(row_width=1)
    fail_markup.add(btn("Попробовать ещё", callback_data=f"filter_again_{mask_input}", emoji=E_PROMO_SEARCH, style="primary"),
                     btn("Назад", callback_data="search_back_to_menu", emoji=E_PROMO_BACK, style="primary"))
    fail_text = (f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Поиск отменён.</b>" if cancelled
                 else f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Ничего не найдено</b>\nПопробуйте другую маску!")
    safe_result_edit(user_id, original_msg.message_id, fail_text, fail_markup)

@bot.callback_query_handler(func=lambda call: call.data.startswith("filter_again_"))
def filter_again_callback(call):
    mask = call.data.split("_",2)[2]; user_id = call.from_user.id
    cd = get_search_cooldown_remaining(user_id)
    if cd > 0:
        bot.answer_callback_query(call.id)
        cd_markup = types.InlineKeyboardMarkup(row_width=1)
        cd_markup.add(btn("Попробовать ещё", callback_data=f"filter_again_{mask}", emoji=E_PROMO_SEARCH, style="primary"))
        try: bot.edit_message_text(f"<b><tg-emoji emoji-id='{E_MAIN}'>⏳</tg-emoji> Подожди {int(cd)+1} сек. перед новым поиском.</b>", user_id, call.message.message_id, parse_mode='HTML', reply_markup=cd_markup)
        except: pass
        return
    if not can_search(user_id):
        try: bot.edit_message_text(no_search_left_text(user_id), user_id, call.message.message_id, parse_mode='HTML', reply_markup=premium_upsell_markup())
        except: pass
        return
    ok, reason = try_start_check(user_id)
    if not ok:
        notify_busy(call, OVERLOAD_TEXT if reason == 'overload' else BUSY_CHECK_TEXT, allow_cancel=(reason == 'already_running'))
        return
    bot.answer_callback_query(call.id)

    def _run():
      try:
        user = get_user(user_id)
        if not user: user, _ = create_user(user_id)
        search_caption = f"<b><tg-emoji emoji-id='{E_MAIN}'>⏰</tg-emoji> Ищу подходящий никнейм...</b>"
        try: bot.delete_message(user_id, call.message.message_id)
        except: pass
        try:
            search_msg = bot.send_message(user_id, search_caption, parse_mode='HTML', reply_markup=cancel_markup())
        except: return
        cancel_ev = register_search(user_id, user_id, search_msg.message_id)

        verify_budget = SessionVerifyBudget()
        def gen_and_check():
            username = "".join(random.choice('abcdefghijklmnopqrstuvwxyz') if ch == '?' else ch for ch in mask if ch == '?' or ch.isalpha())
            if len(username) < 5 or len(username) > 32: return None
            if not passes_checks(user_id, username, verify_budget):
                return None
            return username

        workers = 1
        tasks = [gen_and_check for _ in range(FILTER_ATTEMPTS)]
        username, checked, cancelled = run_candidate_search(user_id, search_msg.message_id, tasks, workers, cancel_ev)
        unregister_search(user_id, cancel_ev)

        if username:
            rating = record_found_username(user_id, username, len(username), user)
            user_last_action[user_id] = time.time()
            win_text = (f"<b><tg-emoji emoji-id='{E_FOUND_NICK}'>✅</tg-emoji> Юзернейм найден.</b>\n\n"
                       f"<blockquote><b><tg-emoji emoji-id='{E_NICK_LABEL}'>📛</tg-emoji> Юзернейм:</b> @{username}\n"
                       f"<b><tg-emoji emoji-id='{E_CLICKABLE}'>🔗</tg-emoji> Кликабельно:</b> <code>{username}</code>\n"
                       f"<b><tg-emoji emoji-id='{E_LETTERS}'>📏</tg-emoji> Кол-во букв:</b> {len(username)}</blockquote>\n\n"
                       f"<b><tg-emoji emoji-id='{E_RATING}'>⭐</tg-emoji> Оценка юзернейма: {rating}/10</b>\n\n"
                       f"<b><tg-emoji emoji-id='{E_CHANNEL_LABEL}'>📢</tg-emoji> Наш канал:</b> {REQUIRED_CHANNEL}")
            fm = types.InlineKeyboardMarkup(row_width=2)
            fm.add(btn("Найти ещё", callback_data=f"filter_again_{mask}", emoji=E_FOUND_NICK, style="success"), btn("Назад", callback_data="search_back_to_menu", emoji=E_PROMO_BACK, style="primary"))
            safe_result_edit(user_id, search_msg.message_id, win_text, fm)
            return
        fail_markup = types.InlineKeyboardMarkup(row_width=1)
        fail_markup.add(btn("Попробовать ещё", callback_data=f"filter_again_{mask}", emoji=E_PROMO_SEARCH, style="primary"),
                         btn("Назад", callback_data="search_back_to_menu", emoji=E_PROMO_BACK, style="primary"))
        fail_text = (f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Поиск отменён.</b>" if cancelled
                     else f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Не удалось найти свободный ник.</b>")
        safe_result_edit(user_id, search_msg.message_id, fail_text, fail_markup)
      finally:
        end_check(user_id)
    threading.Thread(target=_run, daemon=True).start()

@bot.callback_query_handler(func=lambda call: call.data == "search_mode_word")
@subscription_required
def word_search_menu_handler(call):
    user_id = call.from_user.id; bot.answer_callback_query(call.id)
    text = (f"<b><tg-emoji emoji-id='{E_CHOOSE}'>🪧</tg-emoji> Слово</b>\n\n"
            f"<b><tg-emoji emoji-id='{E_MAIN}'>🤔</tg-emoji> Как работает?</b>\n"
            f"<blockquote><b><tg-emoji emoji-id='{E_INFO_LIST}'>📝</tg-emoji> Введите основу (например: robert)\nБот найдет свободные ники с этим корнем\nМинимум 3 английские буквы, максимум 10</b></blockquote>\n\n"
            f"<b><tg-emoji emoji-id='{E_PLANE}'>🎓</tg-emoji> Выберите кнопку ниже:</b>")
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.add(btn("С префиксом", callback_data="word_type_prefix", emoji=E_CHOOSE, style="primary"), btn("С суффиксом", callback_data="word_type_suffix", emoji=E_CHOOSE, style="primary"),
               btn("Рандом", callback_data="word_type_random", emoji=E_CHOOSE, style="primary"), btn("Закрыть", callback_data="search_close", emoji=E_WARN, style="danger"))
    bot.send_message(user_id, text, parse_mode='HTML', reply_markup=markup)

@bot.callback_query_handler(func=lambda call: call.data.startswith("word_type_"))
def word_type_callback(call):
    user_id = call.from_user.id; word_type = call.data.split("_")[2]; bot.answer_callback_query(call.id)
    if not can_search(user_id):
        bot.answer_callback_query(call.id, f"Бесплатные поиски закончились ({FREE_DAILY_SEARCHES}/день). Оформи премиум в разделе «Премиум».", show_alert=True)
        return
    bot.clear_step_handler_by_chat_id(user_id)
    msg = bot.send_message(user_id, f"<b><tg-emoji emoji-id='{E_MAIN}'>📝</tg-emoji> Введите основу слова (3-10 английских букв):</b>", parse_mode='HTML')
    bot.register_next_step_handler(msg, process_word_guarded, word_type)

def process_word_guarded(message, word_type="random"):
    user_id = message.from_user.id
    ok, reason = try_start_check(user_id)
    if not ok:
        bot.send_message(user_id, OVERLOAD_TEXT if reason == 'overload' else BUSY_CHECK_TEXT, parse_mode='HTML',
                         reply_markup=(cancel_markup() if reason == 'already_running' else None))
        return
    def _run():
        try:
            process_word(message, word_type)
        finally:
            end_check(user_id)
    threading.Thread(target=_run, daemon=True).start()

def process_word(message, word_type="random"):
    user_id = message.from_user.id
    if not message.text: bot.send_message(user_id, f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Отправьте текст!</b>", parse_mode='HTML'); return
    cd = get_search_cooldown_remaining(user_id)
    if cd > 0:
        word_for_retry = message.text.strip().lower()
        cd_markup = types.InlineKeyboardMarkup(row_width=1)
        cd_markup.add(btn("Попробовать ещё", callback_data=f"word_again_{word_for_retry}_{word_type}", emoji=E_PROMO_SEARCH, style="primary"))
        bot.send_message(user_id, f"<b><tg-emoji emoji-id='{E_MAIN}'>⏳</tg-emoji> Подожди {int(cd)+1} сек. перед новым поиском.</b>", parse_mode='HTML', reply_markup=cd_markup); return
    if not can_search(user_id):
        bot.send_message(user_id, no_search_left_text(user_id), parse_mode='HTML', reply_markup=premium_upsell_markup()); return
    word = message.text.strip().lower()
    if len(word) < 3 or len(word) > 10 or not all(c in 'abcdefghijklmnopqrstuvwxyz' for c in word):
        bot.send_message(user_id, f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Слово должно быть 3-10 английских букв!</b>", parse_mode='HTML'); return
    user = get_user(user_id)
    if not user: user, _ = create_user(user_id)
    msg = bot.send_message(user_id, f"<b><tg-emoji emoji-id='{E_MAIN}'>⏰</tg-emoji> Ищу подходящий никнейм со словом '{word}'...</b>", parse_mode='HTML', reply_markup=cancel_markup())
    cancel_ev = register_search(user_id, user_id, msg.message_id)
    if word_type == "prefix": combos = [(p, word) for p in prefixes]
    elif word_type == "suffix": combos = [(word, s) for s in suffixes]
    else: combos = [(p, word) for p in prefixes] + [(word, s) for s in suffixes]
    random.shuffle(combos)
    candidates = combos[:SEARCH_ATTEMPTS]

    verify_budget = SessionVerifyBudget()
    def check_combo(pair):
        prefix, suffix = pair
        cand = prefix + suffix
        if len(cand) < 5 or len(cand) > 32: return None
        if not passes_checks(user_id, cand, verify_budget):
            return None
        return cand

    workers = 1
    tasks = [(lambda pair=pair: check_combo(pair)) for pair in candidates]
    username, checked, cancelled = run_candidate_search(user_id, msg.message_id, tasks, workers, cancel_ev)
    unregister_search(user_id, cancel_ev)

    if username:
        rating = record_found_username(user_id, username, len(username), user)
        user_last_action[user_id] = time.time()
        win_text = (f"<b><tg-emoji emoji-id='{E_FOUND_NICK}'>✅</tg-emoji> Юзернейм найден.</b>\n\n"
                   f"<blockquote><b><tg-emoji emoji-id='{E_NICK_LABEL}'>📛</tg-emoji> Юзернейм:</b> @{username}\n"
                   f"<b><tg-emoji emoji-id='{E_CLICKABLE}'>🔗</tg-emoji> Кликабельно:</b> <code>{username}</code>\n"
                   f"<b><tg-emoji emoji-id='{E_LETTERS}'>📏</tg-emoji> Кол-во букв:</b> {len(username)}</blockquote>\n\n"
                   f"<b><tg-emoji emoji-id='{E_RATING}'>⭐</tg-emoji> Оценка юзернейма: {rating}/10</b>\n\n"
                   f"<b><tg-emoji emoji-id='{E_CHANNEL_LABEL}'>📢</tg-emoji> Наш канал:</b> {REQUIRED_CHANNEL}")
        wm = types.InlineKeyboardMarkup(row_width=2)
        wm.add(btn("Найти ещё", callback_data=f"word_again_{word}_{word_type}", emoji=E_FOUND_NICK, style="success"), btn("Назад", callback_data="search_back_to_menu", emoji=E_PROMO_BACK, style="primary"))
        safe_result_edit(user_id, msg.message_id, win_text, wm)
        return
    fail_markup = types.InlineKeyboardMarkup(row_width=1)
    fail_markup.add(btn("Попробовать ещё", callback_data=f"word_again_{word}_{word_type}", emoji=E_PROMO_SEARCH, style="primary"),
                     btn("Назад", callback_data="search_back_to_menu", emoji=E_PROMO_BACK, style="primary"))
    fail_text = (f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Поиск отменён.</b>" if cancelled
                 else f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Ничего не найдено.</b>")
    safe_result_edit(user_id, msg.message_id, fail_text, fail_markup)

@bot.callback_query_handler(func=lambda call: call.data.startswith("word_again_"))
def word_again_callback(call):
    parts = call.data.split("_"); word = parts[2]; word_type = parts[3] if len(parts) > 3 else "random"
    user_id = call.from_user.id
    cd = get_search_cooldown_remaining(user_id)
    if cd > 0:
        try: bot.answer_callback_query(call.id, f"Подожди {int(cd)+1} сек. перед новым поиском.", show_alert=True)
        except: pass
        return
    if not can_search(user_id):
        try: bot.edit_message_text(no_search_left_text(user_id), user_id, call.message.message_id, parse_mode='HTML', reply_markup=premium_upsell_markup())
        except: pass
        return
    ok, reason = try_start_check(user_id)
    if not ok:
        notify_busy(call, OVERLOAD_TEXT if reason == 'overload' else BUSY_CHECK_TEXT, allow_cancel=(reason == 'already_running'))
        return
    try: bot.answer_callback_query(call.id)
    except: pass

    def _run():
      try:
        user = get_user(user_id)
        if not user: user, _ = create_user(user_id)
        try: bot.delete_message(user_id, call.message.message_id)
        except: pass
        try:
            search_msg = bot.send_message(user_id, f"<b><tg-emoji emoji-id='{E_MAIN}'>⏰</tg-emoji> Ищу подходящий никнейм со словом '{word}'...</b>", parse_mode='HTML', reply_markup=cancel_markup())
        except: return
        cancel_ev = register_search(user_id, user_id, search_msg.message_id)
        if word_type == "prefix": combos = [(p, word) for p in prefixes]
        elif word_type == "suffix": combos = [(word, s) for s in suffixes]
        else: combos = [(p, word) for p in prefixes] + [(word, s) for s in suffixes]
        random.shuffle(combos)
        candidates = combos[:SEARCH_ATTEMPTS]

        verify_budget = SessionVerifyBudget()
        def check_combo(pair):
            prefix, suffix = pair
            cand = prefix + suffix
            if len(cand) < 5 or len(cand) > 32: return None
            if not passes_checks(user_id, cand, verify_budget):
                return None
            return cand

        workers = 1
        tasks = [(lambda pair=pair: check_combo(pair)) for pair in candidates]
        username, checked, cancelled = run_candidate_search(user_id, search_msg.message_id, tasks, workers, cancel_ev)
        unregister_search(user_id, cancel_ev)

        if username:
            rating = record_found_username(user_id, username, len(username), user)
            user_last_action[user_id] = time.time()
            win_text = (f"<b><tg-emoji emoji-id='{E_FOUND_NICK}'>✅</tg-emoji> Юзернейм найден.</b>\n\n"
                       f"<blockquote><b><tg-emoji emoji-id='{E_NICK_LABEL}'>📛</tg-emoji> Юзернейм:</b> @{username}\n"
                       f"<b><tg-emoji emoji-id='{E_CLICKABLE}'>🔗</tg-emoji> Кликабельно:</b> <code>{username}</code>\n"
                       f"<b><tg-emoji emoji-id='{E_LETTERS}'>📏</tg-emoji> Кол-во букв:</b> {len(username)}</blockquote>\n\n"
                       f"<b><tg-emoji emoji-id='{E_RATING}'>⭐</tg-emoji> Оценка юзернейма: {rating}/10</b>\n\n"
                       f"<b><tg-emoji emoji-id='{E_CHANNEL_LABEL}'>📢</tg-emoji> Наш канал:</b> {REQUIRED_CHANNEL}")
            wm = types.InlineKeyboardMarkup(row_width=2)
            wm.add(btn("Найти ещё", callback_data=f"word_again_{word}_{word_type}", emoji=E_FOUND_NICK, style="success"), btn("Назад", callback_data="search_back_to_menu", emoji=E_PROMO_BACK, style="primary"))
            safe_result_edit(user_id, search_msg.message_id, win_text, wm)
            return
        fail_markup = types.InlineKeyboardMarkup(row_width=1)
        fail_markup.add(btn("Попробовать ещё", callback_data=f"word_again_{word}_{word_type}", emoji=E_PROMO_SEARCH, style="primary"),
                         btn("Назад", callback_data="search_back_to_menu", emoji=E_PROMO_BACK, style="primary"))
        fail_text = (f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Поиск отменён.</b>" if cancelled
                     else f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Ничего не найдено.</b>")
        safe_result_edit(user_id, search_msg.message_id, fail_text, fail_markup)
      finally:
        end_check(user_id)
    threading.Thread(target=_run, daemon=True).start()

@bot.callback_query_handler(func=lambda call: call.data == "search_trap")
@subscription_required
def search_trap_handler(call):
    user_id = call.from_user.id; bot.answer_callback_query(call.id)
    text = (f"<b><tg-emoji emoji-id='{E_TRAP_TITLE}'>🎯</tg-emoji> Ловушка</b>\n\n"
            f"<b><tg-emoji emoji-id='{E_WARN}'>❓</tg-emoji> Для чего?</b>\n"
            f"<blockquote><tg-emoji emoji-id='{E_TRAP_INFO}'>💡</tg-emoji> Нашел красивый юзернейм, но он занят, ты пишешь занятый юзернейм, и бот сообщит, когда юзернейм станет свободен.</blockquote>")
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.add(btn("Поставить", callback_data="trap_set", emoji=E_TRAP_SET, style="success"),
               btn("Мои ловушки", callback_data="trap_list", emoji=E_TRAP_TITLE, style="primary"),
               btn("Назад", callback_data="search_back_to_menu", emoji=E_PROMO_BACK, style="primary"))
    safe_menu_transition(call, text, markup)

@bot.callback_query_handler(func=lambda call: call.data == "trap_set")
def trap_set_start(call):
    user_id = call.from_user.id; bot.answer_callback_query(call.id)
    with db_lock:
        cursor.execute("SELECT COUNT(*) FROM traps WHERE user_id = ? AND status = 'active'", (user_id,))
        if cursor.fetchone()[0] >= 3:
            bot.send_message(user_id, f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Максимум 3 ловушки!</b>", parse_mode='HTML'); return
    markup = types.InlineKeyboardMarkup(); markup.add(btn("Назад", callback_data="search_back_to_menu", emoji=E_PROMO_BACK, style="primary"))
    bot.clear_step_handler_by_chat_id(user_id)
    msg = bot.send_message(user_id, f"<b><tg-emoji emoji-id='{E_TRAP_INPUT}'>📝</tg-emoji> Введи юзернейм с @ или без. Только английские буквы.</b>", parse_mode='HTML', reply_markup=markup)
    bot.register_next_step_handler(msg, process_trap_set)

def process_trap_set(message):
    user_id = message.from_user.id
    if not message.text: bot.send_message(user_id, f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Отправьте текст!</b>", parse_mode='HTML'); return
    target = message.text.strip().replace('@', '').lower()
    if not target or len(target) < 5 or not all(c in 'abcdefghijklmnopqrstuvwxyz0123456789_' for c in target):
        bot.send_message(user_id, f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Некорректный юзернейм! Разрешены только английские буквы, цифры и подчеркивание.</b>", parse_mode='HTML'); return
    # Раньше можно было поставить ловушку на один и тот же ник несколько раз подряд
    # (случайный повторный клик и т.п.) — в БД копились дубликаты, и check_traps() каждые
    # 10 секунд слал по отдельному HTTP-запросу НА КАЖДУЮ запись, впустую тратя общий
    # rate-limiter/семафор, которым также пользуется активный поиск ников.
    with db_lock:
        cursor.execute("SELECT 1 FROM traps WHERE user_id = ? AND target_username = ? AND status = 'active'", (user_id, target))
        if cursor.fetchone():
            bot.send_message(user_id, f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Вы уже отслеживаете @{target}.</b>", parse_mode='HTML'); return
    if checker.check(target):
        bot.send_message(user_id, f"<b><tg-emoji emoji-id='{E_FOUND_NICK}'>✅</tg-emoji> @{target} уже свободен!</b>\n\n<tg-emoji emoji-id='{E_CLICKABLE}'>🔗</tg-emoji> https://t.me/{target}", parse_mode='HTML'); return
    now = moscow_now().strftime('%Y-%m-%d %H:%M:%S')
    with db_lock: cursor.execute("INSERT INTO traps (user_id, target_username, status, created_date) VALUES (?, ?, 'active', ?)", (user_id, target, now)); conn.commit()
    bot.send_message(user_id, f"<b><tg-emoji emoji-id='{E_TRAP_SET}'>✅</tg-emoji> Юзернейм поставлен.</b>\n\n"
                    f"<blockquote><b><tg-emoji emoji-id='{E_TRAP_NOTIFY}'>🔔</tg-emoji> Как только юзернейм освободиться, я сообщу тебе.</b>\n"
                    f"<b><tg-emoji emoji-id='{E_TRAP_EXPIRE}'>⏳</tg-emoji> Юзернейм будет проверяться 1 неделю (7 дней)</b></blockquote>", parse_mode='HTML')


@bot.callback_query_handler(func=lambda call: call.data == "trap_list")
def trap_list(call):
    user_id = call.from_user.id
    with db_lock: cursor.execute("SELECT target_username, status, created_date FROM traps WHERE user_id = ? ORDER BY created_date DESC", (user_id,)); traps = cursor.fetchall()
    if not traps: text = f"<b><tg-emoji emoji-id='{E_TRAP_TITLE}'>🎯</tg-emoji> У вас нет активных ловушек.</b>"
    else:
        text = f"<b><tg-emoji emoji-id='{E_TRAP_TITLE}'>🎯</tg-emoji> Ваши ловушки:</b>\n\n"
        for t, s, d in traps:
            eid = E_STATS_ACTIVE_SESS if s == 'active' else E_STATS_FLOOD
            text += f"<tg-emoji emoji-id='{eid}'>{'🟢' if s == 'active' else '🔴'}</tg-emoji> @{t} — {s}\n"
    markup = types.InlineKeyboardMarkup(); markup.add(btn("Назад", callback_data="search_back_to_menu", emoji=E_PROMO_BACK, style="primary"))
    safe_edit(call, text, markup)

def check_traps():
    while True:
        time.sleep(60)
        try:
            with db_lock:
                cursor.execute("SELECT id, user_id, target_username, created_date FROM traps WHERE status = 'active'")
                traps = cursor.fetchall()
            if not traps: continue

            active_rows = []
            for row in traps:
                trap_id, user_id, target, created = row
                try:
                    created_dt = datetime.datetime.strptime(created, '%Y-%m-%d %H:%M:%S')
                    if (moscow_now() - created_dt.replace(tzinfo=MOSCOW_TZ)).days > 7:
                        with db_lock: cursor.execute("UPDATE traps SET status = 'expired' WHERE id = ?", (trap_id,)); conn.commit()
                        continue
                except: pass
                active_rows.append(row)

            # Группируем по юзернейму: если один и тот же ник отслеживает несколько людей
            # (или в базе задублировался), раньше на КАЖДУЮ такую запись уходил отдельный
            # HTTP-запрос каждые 10 секунд — впустую тратя общий rate-limiter/семафор,
            # которым также пользуется активный поиск ников. Теперь один уникальный
            # юзернейм проверяется максимум 1 раз за цикл, а результат применяется сразу
            # ко всем ловушкам на этот ник.
            by_username = {}
            for row in active_rows:
                by_username.setdefault(row[2], []).append(row)

            def process_username(item):
                target, rows = item
                if not checker.check(target, use_cache=False, use_fragment=False):
                    return
                ids = [r[0] for r in rows]
                with db_lock:
                    cursor.executemany("UPDATE traps SET status = 'completed' WHERE id = ?", [(i,) for i in ids])
                    conn.commit()
                for trap_id, user_id, _, _ in rows:
                    try:
                        bot.send_message(user_id, f"<b><tg-emoji emoji-id='{E_TRAP_ALERT}'>🚨</tg-emoji> Ловушка сработала!</b>\n\n"
                                        f"<b><tg-emoji emoji-id='{E_TRAP_FREE}'>✅</tg-emoji> Теперь свободен: @{target}</b>\n\n"
                                        f"<b><tg-emoji emoji-id='{E_TRAP_WARN}'>⚠️</tg-emoji> Юзернейм могут занять в любой момент.</b>\n\n<tg-emoji emoji-id='{E_CLICKABLE}'>🔗</tg-emoji> https://t.me/{target}", parse_mode='HTML')
                    except: pass

            with ThreadPoolExecutor(max_workers=20) as ex:
                list(ex.map(process_username, by_username.items()))
        except: pass

threading.Thread(target=check_traps, daemon=True).start()

def premium_left_text(user):
    """Строка с остатком премиума для профиля, либо пустая строка если премиума нет."""
    is_prem = has_premium(user.get('user_id'))
    if not is_prem:
        return ""
    premium_expires = user.get('premium_expires')
    if not premium_expires:
        return f"<b><tg-emoji emoji-id='{E_PREMIUM}'>⭐</tg-emoji> Срок премиума:</b> бессрочно\n"
    try:
        exp_dt = datetime.datetime.strptime(premium_expires, '%Y-%m-%d %H:%M:%S').replace(tzinfo=MOSCOW_TZ)
        delta = exp_dt - moscow_now()
        if delta.total_seconds() <= 0:
            return ""
        d_left = delta.days
        h_left = delta.seconds // 3600
        m_left = (delta.seconds % 3600) // 60
        if d_left > 0:
            left_str = f"{d_left} дн. {h_left} ч."
        elif h_left > 0:
            left_str = f"{h_left} ч. {m_left} мин."
        else:
            left_str = f"{m_left} мин."
        return f"<b><tg-emoji emoji-id='{E_PREMIUM}'>⭐</tg-emoji> Осталось премиума:</b> {left_str} (до {exp_dt.strftime('%d.%m.%Y %H:%M')})\n"
    except:
        return ""

def build_profile_text(user_id, username, user):
    reg_date = user.get('created_date', 'Неизвестно')
    days_in_bot = 0
    if reg_date != 'Неизвестно':
        try:
            reg_dt = datetime.datetime.strptime(reg_date, '%Y-%m-%d %H:%M:%S').replace(tzinfo=MOSCOW_TZ)
            days_in_bot = (moscow_now() - reg_dt).days
            reg_date = reg_dt.strftime('%d.%m.%Y %H:%M')
        except: pass
    display_username = f"@{username}" if username else "Нет"
    is_prem = has_premium(user_id)
    premium_status = f"<tg-emoji emoji-id='{E_FOUND_NICK}'>✅</tg-emoji> Есть" if is_prem else f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Нет"
    premium_left_line = premium_left_text({**user, 'user_id': user_id})
    free_line = "" if is_prem else f"<b><tg-emoji emoji-id='{E_SEARCHES_LABEL}'>🎁</tg-emoji> Бесплатных поисков сегодня:</b> {free_searches_left(user_id)}/{FREE_DAILY_SEARCHES}\n"
    return (f"<b><tg-emoji emoji-id='{E_PROFILE}'>👤</tg-emoji> Твой профиль.</b>\n\n"
            f"<blockquote><b><tg-emoji emoji-id='{E_ID_LABEL}'>🆔</tg-emoji> ID:</b> <code>{user_id}</code>\n"
            f"<b><tg-emoji emoji-id='{E_USERNAME_LABEL}'>📛</tg-emoji> Юзернейм:</b> {display_username}\n"
            f"<b><tg-emoji emoji-id='{E_PREMIUM}'>⭐</tg-emoji> Премиум:</b> {premium_status}\n"
            f"{premium_left_line}{free_line}</blockquote>\n\n"
            f"<b><tg-emoji emoji-id='{E_STATS_TITLE}'>📊</tg-emoji> Ты уже:</b>\n"
            f"<blockquote><b><tg-emoji emoji-id='{E_SEARCHES_LABEL}'>🔍</tg-emoji> Искал юзернеймов:</b> {user.get('total_searches', 0) or 0}\n"
            f"<b><tg-emoji emoji-id='{E_FOUND_LABEL}'>✅</tg-emoji> Нашёл юзернеймов:</b> {user.get('found_count', 0) or 0}\n"
            f"<b><tg-emoji emoji-id='{E_REFS_LABEL}'>👥</tg-emoji> Пригласил друзей:</b> {user.get('referrals_count', 0) or 0}</blockquote>\n\n"
            f"<b><tg-emoji emoji-id='{E_DAYS_IN_BOT}'>📅</tg-emoji> В боте уже:</b> {days_in_bot} дней\n"
            f"<b><tg-emoji emoji-id='{E_FIRST_LOGIN}'>🕐</tg-emoji> Зашёл 1 раз в бота:</b> {reg_date}")

def profile_markup():
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.add(btn("Топ рефералов", callback_data="profile_top_refs", emoji=E_TOP_REF, style="primary"),
               btn("Информация", callback_data="profile_info", emoji=E_INFO_LIST, style="primary"),
               btn("История поиска", callback_data="profile_history", emoji=E_HISTORY, style="primary"),
               btn("Промокод", callback_data="profile_promo", emoji=E_PROMO_STAR, style="primary"))
    return markup

@bot.message_handler(func=lambda m: m.text == "Профиль")
def profile(message):
    user_id = message.from_user.id
    user_last_action[user_id] = time.time()
    user = get_user(user_id)
    if not user: user, _ = create_user(user_id, message.from_user.username)
    text = build_profile_text(user_id, message.from_user.username, user)
    try:
        bot.send_message(user_id, text, parse_mode='HTML', reply_markup=profile_markup())
    except Exception as e:
        logger.error(f"profile: не удалось отправить фото ({e}), шлём текстом")
        bot.send_message(user_id, text, parse_mode='HTML', reply_markup=profile_markup())

@bot.callback_query_handler(func=lambda call: call.data == "profile_history")
def profile_history_callback(call):
    user_id = call.from_user.id; bot.answer_callback_query(call.id)
    with db_lock:
        cursor.execute("SELECT username, length, price, found_date FROM found WHERE finder_id = ? ORDER BY found_date DESC LIMIT 20", (user_id,))
        found_nicks = cursor.fetchall()
    if not found_nicks:
        text = (f"<b><tg-emoji emoji-id='{E_HISTORY}'>📜</tg-emoji> Тут показываются твои недавно найденные ники.</b>\n\n"
               f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Пока что ты ничего не нашёл.</b>")
    else:
        text = (f"<b><tg-emoji emoji-id='{E_HISTORY}'>📜</tg-emoji> Тут показываются твои недавно найденные ники.</b>\n\n"
               f"<b><tg-emoji emoji-id='{E_HISTORY_DESC}'>📋</tg-emoji> Показаны последние 20 найденных:</b>\n\n<blockquote>")
        for username, length, price, found_date in found_nicks:
            text += f"<b><tg-emoji emoji-id='{E_HISTORY_NICK}'>🔹</tg-emoji> @{username}</b> — {price}\n"
        text += "</blockquote>"
    markup = types.InlineKeyboardMarkup(); markup.add(btn("Назад", callback_data="profile_back", emoji=E_PROMO_BACK, style="primary"))
    safe_edit(call, text, markup)

@bot.callback_query_handler(func=lambda call: call.data == "profile_info")
def profile_info_callback(call):
    bot.answer_callback_query(call.id)
    text = (f"<b><tg-emoji emoji-id='{E_WHAT}'>📱</tg-emoji> ДОКУМЕНТАЦИЯ</b>\n\n"
            f"<blockquote><b>Документация бота — это набор руководств, справочных материалов и инструкций, объясняющих, как устроен бот.</b></blockquote>\n\n"
            f"<b><tg-emoji emoji-id='{E_CHOOSE}'>🔎</tg-emoji> Выберите раздел:</b>")
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.add(btn("Конфиденциальная информация", url="https://telegra.ph/Politika-konfidencialnosti-08-26-74", emoji=E_INFO_LIST, style="primary"),
               btn("Пользовательское соглашение", url="https://telegra.ph/Polzovatelskoe-soglashenie-08-26-47", emoji=E_INFO_LIST, style="primary"),
               btn("Назад", callback_data="profile_back", emoji=E_PROMO_BACK, style="primary"))
    safe_edit(call, text, markup)

@bot.callback_query_handler(func=lambda call: call.data == "profile_back")
def profile_back_callback(call):
    user_id = call.from_user.id
    bot.clear_step_handler_by_chat_id(user_id)
    user = get_user(user_id) or {}
    text = build_profile_text(user_id, call.from_user.username, user)
    safe_edit(call, text, profile_markup())

_pending_promo_check = {}  # user_id -> код промокода, ожидающий подтверждения через юзернейм бота в имени профиля

@bot.callback_query_handler(func=lambda call: call.data == "profile_promo")
def profile_promo_callback(call):
    bot.answer_callback_query(call.id)
    _pending_promo_check.pop(call.from_user.id, None)
    text = (f"<b><tg-emoji emoji-id='{E_PROMO_TAG}'>🔖</tg-emoji> Активация промокода</b>\n\n"
            f"<blockquote><b><tg-emoji emoji-id='{E_PROMO_GIFT}'>🎁</tg-emoji> Есть промокод? Отправь его следующим сообщением, и, если он действителен, премиум зачислится автоматически.</b></blockquote>\n\n"
            f"<tg-emoji emoji-id='{E_PROMO_SEARCH}'>🔎</tg-emoji> Для отмены напиши «отмена».")
    markup = types.InlineKeyboardMarkup()
    markup.add(btn("Назад", callback_data="profile_back", emoji=E_PROMO_BACK, style="primary"))
    safe_edit(call, text, markup)
    bot.register_next_step_handler(call.message, process_promo_activate)

def _bot_username_in_name(user_id):
    """Проверяет, содержится ли юзернейм бота в имени/фамилии пользователя (свежие данные из Telegram)."""
    try:
        bot_username = bot.get_me().username or ""
    except:
        bot_username = ""
    if not bot_username:
        return False
    try:
        chat = bot.get_chat(user_id)
        full_name = f"{chat.first_name or ''} {chat.last_name or ''}"
    except:
        return False
    return bot_username.lower() in full_name.lower()

def promo_name_check_markup():
    markup = types.InlineKeyboardMarkup(row_width=1)
    markup.add(btn("Проверить", callback_data="promo_check_name", emoji=E_PROMO_OK, style="success"),
               btn("Отмена", callback_data="promo_name_cancel", emoji=E_PROMO_BACK, style="danger"))
    return markup

def promo_name_check_text(code):
    bot_username = bot.get_me().username or "bot"
    return (f"<blockquote><b><tg-emoji emoji-id='{E_PROMO_GEAR}'>⚙️</tg-emoji> Чтобы активировать промокод <code>{code}</code>, добавь юзернейм бота <code>@{bot_username}</code> в своё имя профиля Telegram.</b></blockquote>\n\n"
            f"<b><tg-emoji emoji-id='{E_PROMO_PIC}'>🖼</tg-emoji> Как это сделать:</b>\n"
            f"<blockquote><b>1.</b> Открой «Настройки» в Telegram\n"
            f"<b>2.</b> Нажми «Изменить имя»\n"
            f"<b>3.</b> Допиши <code>@{bot_username}</code> к своему имени и сохрани</blockquote>\n\n"
            f"<tg-emoji emoji-id='{E_PROMO_SEARCH}'>🔎</tg-emoji> Когда добавишь — нажми «Проверить».")

def _promo_code_exists(code):
    """Проверяет, существовал ли когда-либо такой промокод (независимо от лимита/активности)."""
    with db_lock:
        cursor.execute("SELECT 1 FROM promocodes WHERE code=?", (code,))
        return cursor.fetchone() is not None

def _promo_lock_error(user_id):
    """Если премиум получен по промокоду (premium_source == 'promo') и срок ещё не истёк —
    новый промокод активировать нельзя. Если премиум куплен/выдан не по промокоду —
    блокировки нет, новый промокод активировать можно (срок при этом просто продлевается).
    Возвращает готовый HTML-текст ошибки или None, если блокировки нет."""
    user = get_user(user_id)
    if not user or user.get('premium_source') != 'promo':
        return None
    expires = user.get('premium_expires')
    if not expires:
        return None
    try:
        exp_dt = datetime.datetime.strptime(expires, '%Y-%m-%d %H:%M:%S').replace(tzinfo=MOSCOW_TZ)
    except Exception:
        return None
    if exp_dt <= moscow_now():
        return None
    return (f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> У тебя уже активирован промокод.</b>\n\n"
            f"<blockquote>Новый промокод можно будет активировать после {exp_dt.strftime('%d.%m.%Y %H:%M')}, "
            f"когда закончится текущий срок премиума.</blockquote>")

def process_promo_activate(message):
    user_id = message.from_user.id
    if not message.text: return
    raw = message.text.strip()
    if raw.lower() == 'отмена':
        _pending_promo_check.pop(user_id, None)
        send_html_safe(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Отменено", reply_markup=profile_markup()); return
    code = re.sub(r'\s+', '', raw).upper()
    if not _promo_code_exists(code):
        send_html_safe(message.chat.id,
            f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Такого промокода не существует.</b>\n\n<i>Проверь правильность ввода и попробуй ещё раз.</i>",
            reply_markup=profile_markup())
        return
    lock_error = _promo_lock_error(user_id)
    if lock_error:
        send_html_safe(message.chat.id, lock_error, reply_markup=profile_markup())
        return
    user = get_user(user_id)
    if not user: user, _ = create_user(user_id, message.from_user.username)
    if _bot_username_in_name(user_id):
        _activate_promo(message.chat.id, user_id, code)
        return
    _pending_promo_check[user_id] = code
    send_html_safe(message.chat.id, promo_name_check_text(code), reply_markup=promo_name_check_markup())

@bot.callback_query_handler(func=lambda call: call.data == "promo_check_name")
def promo_check_name_callback(call):
    user_id = call.from_user.id
    code = _pending_promo_check.get(user_id)
    if not code:
        bot.answer_callback_query(call.id, "❌ Сессия активации истекла, введите промокод заново.", show_alert=True)
        return
    if not _bot_username_in_name(user_id):
        bot.answer_callback_query(call.id, "❌ Юзернейм бота не найден в имени профиля!", show_alert=True)
        return
    bot.answer_callback_query(call.id)
    _pending_promo_check.pop(user_id, None)
    _activate_promo(call.message.chat.id, user_id, code, edit_call=call)

@bot.callback_query_handler(func=lambda call: call.data == "promo_name_cancel")
def promo_name_cancel_callback(call):
    bot.answer_callback_query(call.id)
    _pending_promo_check.pop(call.from_user.id, None)
    safe_edit(call, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Отменено", profile_markup())

def _activate_promo(chat_id, user_id, code, edit_call=None):
    """Атомарно (под одним db_lock) проверяет промокод и сразу же резервирует место активации.
    Раньше проверка лимита и списание были разнесены по времени: несколько пользователей могли
    одновременно пройти проверку "лимит не исчерпан" ещё до того, как кто-то из них реально
    списал место — в итоге при гонке за последний слот могли активироваться все, а не только
    один. Здесь SELECT лимита + проверка повторной активации + INSERT + UPDATE счётчика идут
    одним блоком под db_lock (RLock), так что никакой другой поток не может вклиниться между
    проверкой и списанием — слот гарантированно достаётся только одному.
    Если передан edit_call — результат редактирует существующее сообщение (колбэк), иначе шлёт новое."""
    now_str = moscow_now().strftime('%Y-%m-%d %H:%M:%S')
    lock_error = _promo_lock_error(user_id)
    if lock_error:
        _pending_promo_check.pop(user_id, None)
        if edit_call is not None:
            safe_edit(edit_call, lock_error, profile_markup())
        else:
            send_html_safe(chat_id, lock_error, reply_markup=profile_markup())
        return
    if not _bot_username_in_name(user_id):
        # Финальный барьер прямо перед начислением: без юзернейма бота в нике
        # промокод не активируется, независимо от того, каким путём сюда попали
        # (кнопка «Проверить» или прямой ввод кода) — исключает гонки/устаревшие проверки.
        name_error = f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Юзернейм бота не найден в имени профиля!</b>\n\n<i>Добавь его в имя и попробуй снова.</i>"
        _pending_promo_check.pop(user_id, None)
        if edit_call is not None:
            safe_edit(edit_call, name_error, profile_markup())
        else:
            send_html_safe(chat_id, name_error, reply_markup=profile_markup())
        return
    with db_lock:
        cursor.execute("SELECT code, days, max_activations, activations_count, active FROM promocodes WHERE code=?", (code,))
        row = cursor.fetchone()
        if not row:
            error = f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Такого промокода не существует.</b>\n\n<i>Проверь правильность ввода и попробуй ещё раз.</i>"
            days = None
        else:
            _, days, max_act, used, active = row
            if not active or (max_act is not None and used >= max_act):
                error = f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Промокод больше не действует — закончился лимит активаций.</b>"
            else:
                cursor.execute("SELECT 1 FROM promo_activations WHERE code=? AND user_id=?", (code, user_id))
                if cursor.fetchone():
                    error = f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Ты уже активировал этот промокод ранее.</b>"
                else:
                    try:
                        cursor.execute("INSERT INTO promo_activations (code, user_id, activated_at) VALUES (?,?,?)", (code, user_id, now_str))
                        cursor.execute("UPDATE promocodes SET activations_count = activations_count + 1 WHERE code=?", (code,))
                        conn.commit()
                        error = None
                    except sqlite3.IntegrityError:
                        conn.rollback()
                        error = f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Ты уже активировал этот промокод ранее.</b>"
    _pending_promo_check.pop(user_id, None)
    if error:
        if edit_call is not None:
            safe_edit(edit_call, error, profile_markup())
        else:
            send_html_safe(chat_id, error, reply_markup=profile_markup())
        return
    user = get_user(user_id)
    current_expires = user.get('premium_expires')
    if current_expires:
        try:
            exp_dt = datetime.datetime.strptime(current_expires, '%Y-%m-%d %H:%M:%S').replace(tzinfo=MOSCOW_TZ)
            new_expires = (exp_dt if exp_dt > moscow_now() else moscow_now()) + datetime.timedelta(days=days)
        except:
            new_expires = moscow_now() + datetime.timedelta(days=days)
    else:
        new_expires = moscow_now() + datetime.timedelta(days=days)
    update_user(user_id, is_premium=1, premium_expires=new_expires.strftime('%Y-%m-%d %H:%M:%S'), premium_source='promo')
    text = (f"<b><tg-emoji emoji-id='{E_PROMO_OK}'>✔️</tg-emoji> Промокод активирован!</b>\n\n"
            f"<blockquote><b><tg-emoji emoji-id='{E_PROMO_TAG}'>🔖</tg-emoji> Код:</b> <code>{code}</code>\n"
            f"<b><tg-emoji emoji-id='{E_PROMO_STAR}'>⭐</tg-emoji> Начислено:</b> {days} дн. премиума\n"
            f"<b><tg-emoji emoji-id='{E_PROMO_STAR2}'>⭐</tg-emoji> Истекает:</b> {new_expires.strftime('%d.%m.%Y %H:%M')}</blockquote>\n\n"
            f"<b><tg-emoji emoji-id='{E_PROMO_GIFT}'>🎁</tg-emoji> Наслаждайся премиум-возможностями бота!</b>")
    if edit_call is not None:
        safe_edit(edit_call, text, profile_markup())
    else:
        send_html_safe(chat_id, text, reply_markup=profile_markup())
    try:
        bot.send_message(ADMIN_ID, f"<tg-emoji emoji-id='{E_PROMO_TAG}'>🔖</tg-emoji> Промокод <code>{code}</code> активирован пользователем ID {user_id} (+{days} дн.)", parse_mode='HTML')
    except: pass

def get_top_refs():
    with db_lock:
        cursor.execute("SELECT username, user_id, referrals_count FROM users WHERE referrals_count > 0 AND banned = 0 ORDER BY referrals_count DESC")
        all_refs = cursor.fetchall()
        cursor.execute("SELECT username FROM top_ref_excluded")
        excluded_usernames = {row[0] for row in cursor.fetchall()}
    top = []
    for username, user_id, refs in all_refs:
        if username and username in excluded_usernames: continue
        if not check_channel_subscription(user_id): continue
        current_username = username
        try:
            chat_member = bot.get_chat_member(user_id, user_id)
            if chat_member.user.username:
                current_username = chat_member.user.username
                if current_username != username:
                    with db_lock: cursor.execute("UPDATE users SET username=? WHERE user_id=?", (current_username, user_id)); conn.commit()
        except: pass
        top.append({'username': current_username or f"ID{user_id}", 'refs': refs})
        if len(top) >= 10: break
    return top

@bot.callback_query_handler(func=lambda call: call.data == "profile_top_refs")
def profile_top_refs_callback(call):
    top = get_top_refs()
    if not top: text = f"<b><tg-emoji emoji-id='{E_TOP_REF}'>🏆</tg-emoji> Топ рефералов</b>\n\n<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Пока нет участников"
    else:
        text = f"<b><tg-emoji emoji-id='{E_TOP_REF}'>🏆</tg-emoji> Топ рефералов</b>\n\n<blockquote>"
        for i, user in enumerate(top, 1):
            name = f"@{user['username']}" if not user['username'].startswith('ID') else user['username']
            text += f"<b><tg-emoji emoji-id='{E_TOP_REF_PLACE}'>⭐</tg-emoji> {i} место: {name} — {user['refs']} Реф.</b>\n"
        text += "</blockquote>"
    markup = types.InlineKeyboardMarkup(); markup.add(btn("Назад", callback_data="profile_back", emoji=E_PROMO_BACK, style="primary"))
    safe_edit(call, text, markup)

@bot.message_handler(func=lambda m: m.text == "Рефералка")
def referral_button_handler(message):
    user_id = message.from_user.id; user_last_action[user_id] = time.time()
    user = get_user(user_id)
    if not user: user, _ = create_user(user_id, message.from_user.username)
    link = f"https://t.me/{bot.get_me().username}?start={user_id}"
    total_refs = user.get('referrals_count', 0) or 0
    progress = total_refs % REFERRALS_FOR_PREMIUM  # 0..N-1: сколько накоплено к текущему кругу; после каждых N — снова с 0
    share_text = "Привет, я использую бота Vertex, для поиска свободных юзернеймов, присоединяйся"
    text = (f"<b><tg-emoji emoji-id='{E_REF_TOP}'>👥</tg-emoji> Здесь ты можешь пригласить друга в бота.</b>\n\n"
            f"<b><tg-emoji emoji-id='{E_REF_LINK}'>🔗</tg-emoji> Твоя реферальная ссылка:</b>\n<b><code>{link}</code></b>\n\n"
            f"<blockquote><b><tg-emoji emoji-id='{E_PREMIUM}'>⭐</tg-emoji> Осталось до премиума: {progress}/{REFERRALS_FOR_PREMIUM}</b>\n"
            f"<b><tg-emoji emoji-id='{E_REFS_LABEL}'>👥</tg-emoji> Всего пригласил: {total_refs}</b></blockquote>\n\n"
            f"<b><tg-emoji emoji-id='{E_PREMIUM}'>⭐</tg-emoji> За каждые {REFERRALS_FOR_PREMIUM} рефералов — {REFERRAL_PREMIUM_DAYS} день премиума бесплатно!</b>\n\n"
            f"<b><tg-emoji emoji-id='{E_REF_SHARE}'>📤</tg-emoji> Нажми на кнопку ниже чтобы поделиться ботом.</b>")
    markup = types.InlineKeyboardMarkup()
    from urllib.parse import quote
    markup.add(btn("Поделиться", url=f"https://t.me/share/url?url={quote(link, safe='')}&text={quote(share_text)}", emoji=E_REF_SHARE, style="primary"))
    bot.send_message(user_id, text, parse_mode='HTML', reply_markup=markup)

@bot.message_handler(func=lambda m: m.text == "Панель управления")
def admin_button(message):
    if message.from_user.id != ADMIN_ID: return
    ram_used = get_ram_usage(); cpu = get_cpu_usage()
    text = (f"<b><tg-emoji emoji-id='{E_ADMIN_MENU}'>⚙️</tg-emoji> Меню администратора</b>\n\n"
            f"<b><tg-emoji emoji-id='{E_ADMIN_BOT_MODE}'>🔧</tg-emoji> Бот работает в {'боевом' if not MAINTENANCE_MODE else 'техническом'} режиме</b>\n\n"
            f"<blockquote><b><tg-emoji emoji-id='{E_ADMIN_RAM}'>📊</tg-emoji> Оперативки занято: {cpu}</b>\n"
            f"<b><tg-emoji emoji-id='{E_ADMIN_RAM}'>📊</tg-emoji> Памяти занято: {ram_used}</b></blockquote>\n\n"
            f"<b><tg-emoji emoji-id='{E_ADMIN_CHOOSE}'>📋</tg-emoji> Выберите раздел ниже</b>")
    bot.send_message(message.chat.id, text, parse_mode='HTML', reply_markup=admin_inline_menu())

@bot.callback_query_handler(func=lambda call: call.data == "admin_back")
def admin_back_callback(call):
    if call.from_user.id != ADMIN_ID: return
    bot.clear_step_handler_by_chat_id(call.message.chat.id)
    _broadcast_drafts.pop(call.message.chat.id, None)
    ram_used = get_ram_usage(); cpu = get_cpu_usage()
    text = (f"<b><tg-emoji emoji-id='{E_ADMIN_MENU}'>⚙️</tg-emoji> Меню администратора</b>\n\n"
            f"<b><tg-emoji emoji-id='{E_ADMIN_BOT_MODE}'>🔧</tg-emoji> Бот работает в {'боевом' if not MAINTENANCE_MODE else 'техническом'} режиме</b>\n\n"
            f"<blockquote><b><tg-emoji emoji-id='{E_ADMIN_RAM}'>📊</tg-emoji> Оперативки занято: {cpu}</b>\n"
            f"<b><tg-emoji emoji-id='{E_ADMIN_RAM}'>📊</tg-emoji> Памяти занято: {ram_used}</b></blockquote>\n\n"
            f"<b><tg-emoji emoji-id='{E_ADMIN_CHOOSE}'>📋</tg-emoji> Выберите раздел ниже</b>")
    safe_edit(call, text, admin_inline_menu())

@bot.callback_query_handler(func=lambda call: call.data == "admin_toggle_session_search")
def admin_toggle_session_search(call):
    global SESSION_SEARCH_ENABLED
    if call.from_user.id != ADMIN_ID: return
    SESSION_SEARCH_ENABLED = not SESSION_SEARCH_ENABLED
    save_setting('session_search_enabled', '1' if SESSION_SEARCH_ENABLED else '0')
    bot.answer_callback_query(call.id, f"Поиск с сессиями {'ВКЛ' if SESSION_SEARCH_ENABLED else 'ВЫКЛ'}", show_alert=True)

@bot.callback_query_handler(func=lambda call: call.data == "admin_toggle_maintenance")
def admin_toggle_maintenance(call):
    global MAINTENANCE_MODE
    if call.from_user.id != ADMIN_ID: return
    MAINTENANCE_MODE = not MAINTENANCE_MODE
    bot.answer_callback_query(call.id, f"Тех-работы {'включены' if MAINTENANCE_MODE else 'выключены'}", show_alert=True)

@bot.callback_query_handler(func=lambda call: call.data == "admin_remove_top_ref")
def admin_remove_top_ref_callback(call):
    if call.from_user.id != ADMIN_ID: return
    msg = bot.send_message(call.message.chat.id, f"<tg-emoji emoji-id='{E_BANNED}'>🚫</tg-emoji> Введите юзернейм (без @), которого нужно убрать из топа рефералов:", parse_mode='HTML')
    bot.register_next_step_handler(msg, process_remove_top_ref)

def process_remove_top_ref(message):
    if message.from_user.id != ADMIN_ID: return
    username = message.text.strip().replace('@', '').lower()
    if not username: bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Введите юзернейм!", reply_markup=admin_inline_menu(), parse_mode='HTML'); return
    with db_lock: cursor.execute("INSERT OR IGNORE INTO top_ref_excluded (username) VALUES (?)", (username,)); conn.commit()
    bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_FOUND_NICK}'>✅</tg-emoji> @{username} убран из топа рефералов", reply_markup=admin_inline_menu(), parse_mode='HTML')

@bot.callback_query_handler(func=lambda call: call.data == "admin_stats")
def admin_stats_callback(call):
    if call.from_user.id != ADMIN_ID: return
    with db_lock:
        cursor.execute("SELECT COUNT(*) FROM users"); total_users = cursor.fetchone()[0]
        cursor.execute("SELECT SUM(total_searches) FROM users"); total_searches = cursor.fetchone()[0] or 0
        cursor.execute("SELECT SUM(found_count) FROM users"); total_found = cursor.fetchone()[0] or 0
        cursor.execute("SELECT COUNT(*) FROM users WHERE banned=1"); banned = cursor.fetchone()[0]
        now_str = moscow_now().strftime('%Y-%m-%d %H:%M:%S')
        cursor.execute("SELECT COUNT(*) FROM users WHERE is_premium=1 AND (premium_expires IS NULL OR premium_expires > ?)", (now_str,)); premium_now = cursor.fetchone()[0]
    ss = session_manager.get_status(); tc = session_manager.stats['checks_total']; fc = session_manager.stats['checks_free']
    acc = round((fc/tc*100), 2) if tc else 0
    text = (f"<b><tg-emoji emoji-id='{E_STATS_TITLE}'>📊</tg-emoji> СТАТИСТИКА</b>\n\n"
            f"<blockquote><b><tg-emoji emoji-id='{E_STATS_TOTAL}'>👥</tg-emoji> Всего людей: {total_users}</b>\n"
            f"<b><tg-emoji emoji-id='{E_STATS_BANNED}'>🚫</tg-emoji> Забанено: {banned}</b>\n"
            f"<b><tg-emoji emoji-id='{E_STATS_SEARCHES}'>🔍</tg-emoji> Поисков: {total_searches}</b>\n"
            f"<b><tg-emoji emoji-id='{E_STATS_FOUND}'>✅</tg-emoji> Найдено: {total_found}</b>\n"
            f"<b><tg-emoji emoji-id='{E_PREMIUM}'>⭐</tg-emoji> Премиум сейчас: {premium_now}</b></blockquote>\n\n"
            f"<blockquote><b><tg-emoji emoji-id='{E_STATS_ACTIVE_SESS}'>🟢</tg-emoji> Активных: {ss['active']}</b>\n"
            f"<b><tg-emoji emoji-id='{E_STATS_WAITING}'>🟡</tg-emoji> Ожидают: {ss['waiting']}</b>\n"
            f"<b><tg-emoji emoji-id='{E_STATS_FLOOD}'>🔴</tg-emoji> В флуде: {ss['flood']}</b>\n"
            f"<b><tg-emoji emoji-id='{E_STATS_INVALID}'>⚫</tg-emoji> Невалид: {ss['invalid']}</b>\n"
            f"<b><tg-emoji emoji-id='{E_STATS_TOTAL_SESS}'>📱</tg-emoji> Всего: {ss['total']}</b>\n"
            f"<b><tg-emoji emoji-id='{E_STATS_CHECKS}'>🔍</tg-emoji> Проверок: {tc}</b>\n"
            f"<b><tg-emoji emoji-id='{E_STATS_ACCURACY}'>🎯</tg-emoji> Точность: {acc}%</b></blockquote>")
    safe_edit(call, text, admin_inline_menu())

@bot.callback_query_handler(func=lambda call: call.data == "admin_report")
def admin_report_callback(call):
    if call.from_user.id != ADMIN_ID: return
    reset_daily_stats_if_new_day()
    today = moscow_now().strftime('%Y-%m-%d'); today_date = moscow_now().strftime('%d.%m.%Y')
    with db_lock:
        today_start = moscow_today_start().strftime('%Y-%m-%d %H:%M:%S')
        cursor.execute("SELECT COUNT(*) FROM users WHERE created_date >= ?", (today_start,)); new_users = cursor.fetchone()[0]
        cursor.execute("SELECT COUNT(*) FROM users WHERE created_date >= ? AND referral_activated = 1", (today_start,)); new_ref = cursor.fetchone()[0]
        cursor.execute("SELECT COUNT(*) FROM found WHERE found_date >= ?", (today_start,)); found_today = cursor.fetchone()[0]
        cursor.execute("SELECT COUNT(*) FROM crypto_invoices WHERE status='paid' AND created_at >= ?", (today_start,)); crypto_bought_today = cursor.fetchone()[0]
        cursor.execute("SELECT COUNT(*) FROM priemka_transactions WHERE status='credited' AND created_at >= ?", (today_start,)); stars_bought_today = cursor.fetchone()[0]
    premium_bought_today = crypto_bought_today + stars_bought_today
    text = (f"<b><tg-emoji emoji-id='{E_ADMIN_REPORT}'>📊</tg-emoji> Отчёт за сегодня ({today_date})</b>\n\n"
            f"<blockquote><b><tg-emoji emoji-id='{E_ADMIN_NEW_USERS}'>👥</tg-emoji> Новых людей: {new_users}</b>\n"
            f"<b><tg-emoji emoji-id='{E_ADMIN_NEW_REF}'>🔗</tg-emoji> Новых с реф. ссылки: {new_ref}</b>\n"
            f"<b><tg-emoji emoji-id='{E_ADMIN_FOUND_NICKS}'>✅</tg-emoji> Найдено ников: {found_today}</b>\n"
            f"<b><tg-emoji emoji-id='{E_PREMIUM}'>⭐</tg-emoji> Куплено премиума сегодня: {premium_bought_today}</b></blockquote>")
    safe_edit(call, text, admin_inline_menu())

temp_sessions = {}

def sessions_admin_menu():
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.add(btn("Добавить", callback_data="sessions_add", emoji=E_SESSION_ADD, style="success"), btn("Список", callback_data="sessions_list", emoji=E_SESSION_LIST, style="primary"),
               btn("Перезагрузить", callback_data="sessions_reload", emoji=E_SETTINGS, style="primary"), btn("Статус", callback_data="sessions_status", emoji=E_SESSION_STATUS, style="primary"),
               btn("Удалить", callback_data="sessions_delete", emoji=E_SESSION_DELETE, style="danger"), btn("Назад", callback_data="admin_back", emoji=E_PROMO_BACK, style="primary"))
    return markup

@bot.callback_query_handler(func=lambda call: call.data == "admin_sessions")
def admin_sessions_menu(call):
    if call.from_user.id != ADMIN_ID: return
    ss = session_manager.get_status(); tc = session_manager.stats['checks_total']; fc = session_manager.stats['checks_free']
    bc = session_manager.stats['checks_banned']; kc = session_manager.stats['checks_taken']; ec = session_manager.stats['checks_error']
    acc = round((fc/tc*100), 1) if tc else 0
    text = (f"<b><tg-emoji emoji-id='{E_SESSIONS_TITLE}'>🎭</tg-emoji> Управление сессиями</b>\n\n"
            f"<blockquote><b><tg-emoji emoji-id='{E_SESSIONS_ACTIVE}'>📊</tg-emoji> Активных: {ss['active']}</b>\n"
            f"<b><tg-emoji emoji-id='{E_SESSIONS_ACTIVE}'>📊</tg-emoji> В ожидании: {ss['waiting']}</b>\n"
            f"<b><tg-emoji emoji-id='{E_SESSIONS_ACTIVE}'>📊</tg-emoji> В флуде: {ss['flood']}</b>\n"
            f"<b><tg-emoji emoji-id='{E_SESSIONS_ACTIVE}'>📊</tg-emoji> Слетело: {ss['invalid']}</b>\n"
            f"<b><tg-emoji emoji-id='{E_SESSIONS_ACTIVE}'>📊</tg-emoji> Всего: {ss['total']}</b>\n"
            f"<b><tg-emoji emoji-id='{E_SESSIONS_CHECKS}'>🔍</tg-emoji> Проверок: {tc} (free {fc} / taken {kc} / banned {bc} / error {ec})</b></blockquote>\n\n<b>🎯 Точность: {acc}%</b>")
    safe_edit(call, text, sessions_admin_menu())

@bot.callback_query_handler(func=lambda call: call.data == "sessions_add")
def sessions_add_phone(call):
    if call.from_user.id != ADMIN_ID: return
    text = (f"<b><tg-emoji emoji-id='{E_SESSION_ADD}'>📱</tg-emoji> Добавление номера</b>\n\n"
            f"<b><tg-emoji emoji-id='{E_SESSION_ADD_DESC}'>📝</tg-emoji> Введи номер с + или без</b>")
    markup = types.InlineKeyboardMarkup(row_width=1); markup.add(btn("Отменить", callback_data="admin_sessions", emoji=E_WARN, style="danger"))
    msg = bot.send_message(call.message.chat.id, text, parse_mode='HTML', reply_markup=markup)
    bot.register_next_step_handler(msg, process_phone)

def process_phone(message):
    if message.from_user.id != ADMIN_ID: return
    user_id = message.from_user.id
    if not message.text: bot.send_message(user_id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Отправьте текст!", parse_mode='HTML'); return
    phone = message.text.strip().replace(' ', '').replace('-', '')
    if phone.lower() == 'отмена': bot.send_message(user_id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Отменено", reply_markup=admin_inline_menu(), parse_mode='HTML'); return
    if not phone.startswith('+'): phone = '+' + phone
    if not phone[1:].isdigit(): bot.send_message(user_id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Неверный формат", parse_mode='HTML'); return
    with db_lock:
        cursor.execute("SELECT id FROM sessions WHERE phone=?", (phone,))
        if cursor.fetchone(): bot.send_message(user_id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> {phone} уже добавлен!", reply_markup=admin_inline_menu(), parse_mode='HTML'); return
    msg = bot.send_message(user_id, f"🔄 Подключаюсь к {phone}...", parse_mode='HTML')
    async def connect_and_send():
        client = TelegramClient(StringSession(), API_ID, API_HASH); await client.connect(); await client.send_code_request(phone); return client
    try:
        client = run_async(connect_and_send()); temp_sessions[user_id] = {"phone": phone, "client": client, "step": "waiting_code"}
        bot.edit_message_text(f"<tg-emoji emoji-id='{E_FOUND_NICK}'>✅</tg-emoji> Код отправлен на {phone}\n\n<tg-emoji emoji-id='{E_SESSION_ADD}'>📱</tg-emoji> Введите код:", user_id, msg.message_id, parse_mode='HTML')
        bot.register_next_step_handler(msg, process_code)
    except Exception as e: bot.edit_message_text(f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Ошибка: {str(e)}", user_id, msg.message_id, parse_mode='HTML')

def process_code(message):
    if message.from_user.id != ADMIN_ID: return
    user_id = message.from_user.id
    if not message.text: return
    code = message.text.strip()
    if code.lower() == 'отмена': _cleanup(user_id); bot.send_message(user_id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Отменено", reply_markup=admin_inline_menu(), parse_mode='HTML'); return
    if not code.isdigit(): bot.send_message(user_id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Только цифры", parse_mode='HTML'); return
    sd = temp_sessions.get(user_id)
    if not sd: bot.send_message(user_id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Сессия не найдена", reply_markup=admin_inline_menu(), parse_mode='HTML'); return
    client = sd["client"]; phone = sd["phone"]
    msg = bot.send_message(user_id, "🔄 Проверяю код...", parse_mode='HTML')
    async def sign_in(): await client.sign_in(phone, code); return client.session.save()
    try:
        session_string = run_async(sign_in()); _save_session(session_string, phone, user_id, msg.message_id)
    except errors.SessionPasswordNeededError:
        bot.edit_message_text(f"🔐 <b>Требуется 2FA пароль</b>\n\nВведите облачный пароль от {phone}:", user_id, msg.message_id, parse_mode='HTML')
        temp_sessions[user_id]["step"] = "waiting_password"; bot.register_next_step_handler(msg, process_password)
    except errors.PhoneCodeInvalidError:
        bot.edit_message_text(f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> <b>Неверный код</b>\n\nПопробуйте ещё раз:", user_id, msg.message_id, parse_mode='HTML')
        bot.register_next_step_handler(msg, process_code)
    except Exception as e: bot.edit_message_text(f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Ошибка: {str(e)}", user_id, msg.message_id, parse_mode='HTML'); _cleanup(user_id)

def process_password(message):
    if message.from_user.id != ADMIN_ID: return
    user_id = message.from_user.id
    if not message.text: return
    password = message.text.strip()
    if password.lower() == 'отмена': _cleanup(user_id); bot.send_message(user_id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Отменено", reply_markup=admin_inline_menu(), parse_mode='HTML'); return
    sd = temp_sessions.get(user_id)
    if not sd: bot.send_message(user_id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Сессия не найдена", reply_markup=admin_inline_menu(), parse_mode='HTML'); return
    client = sd["client"]; phone = sd["phone"]
    msg = bot.send_message(user_id, "🔄 Проверяю пароль...", parse_mode='HTML')
    async def sign_in_password(): await client.sign_in(password=password); return client.session.save()
    try:
        session_string = run_async(sign_in_password()); _save_session(session_string, phone, user_id, msg.message_id)
    except errors.PasswordHashInvalidError:
        bot.edit_message_text(f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> <b>Неверный пароль</b>\n\nПопробуйте ещё раз:", user_id, msg.message_id, parse_mode='HTML')
        bot.register_next_step_handler(msg, process_password)
    except Exception as e: bot.edit_message_text(f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Ошибка: {str(e)}", user_id, msg.message_id, parse_mode='HTML'); _cleanup(user_id)

def _save_session(session_string, phone, user_id, msg_id):
    try:
        now = moscow_now().strftime('%Y-%m-%d %H:%M:%S')
        with db_lock: cursor.execute("INSERT INTO sessions (phone, session_string, status, created_at, updated_at) VALUES (?,?,'waiting',?,?)", (phone, session_string, now, now)); conn.commit()
        session_manager.load_from_db()
        bot.edit_message_text(f"<tg-emoji emoji-id='{E_FOUND_NICK}'>✅</tg-emoji> <b>Аккаунт {phone} добавлен!</b>", user_id, msg_id, parse_mode='HTML', reply_markup=admin_inline_menu())
        _cleanup(user_id)
    except Exception as e: bot.edit_message_text(f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Ошибка сохранения: {str(e)}", user_id, msg_id, parse_mode='HTML'); _cleanup(user_id)

def _cleanup(user_id):
    if user_id in temp_sessions:
        client = temp_sessions[user_id].get("client")
        if client:
            try: run_async(client.disconnect())
            except: pass
        del temp_sessions[user_id]

@bot.callback_query_handler(func=lambda call: call.data == "sessions_list")
def sessions_list(call):
    if call.from_user.id != ADMIN_ID: return
    with db_lock: cursor.execute("SELECT id, phone, status FROM sessions ORDER BY id DESC"); sessions = cursor.fetchall()
    if sessions:
        text = f"<b><tg-emoji emoji-id='{E_SESSION_LIST}'>📋</tg-emoji> Список сессий</b>\n\n<blockquote>"
        for i, p, s in sessions:
            eid = E_SESSION_ACTIVE if s == 'active' else E_SESSION_WAITING if s == 'waiting' else E_SESSION_FLOOD if s == 'flood' else E_STATS_INVALID
            st = 'Активна' if s == 'active' else 'Ожидание' if s == 'waiting' else 'Флуд' if s == 'flood' else 'Забанена' if s == 'banned' else 'Невалид'
            text += f"<b><tg-emoji emoji-id='{eid}'>📱</tg-emoji> {p or f'ID{i}'} — {st}</b>\n"
        text += "</blockquote>"
    else: text = f"<b><tg-emoji emoji-id='{E_SESSION_LIST}'>📋</tg-emoji> Список сессий</b>\n\nНет сессий"
    markup = types.InlineKeyboardMarkup(); markup.add(btn("Назад", callback_data="admin_sessions", emoji=E_PROMO_BACK, style="primary"))
    safe_edit(call, text, markup)

@bot.callback_query_handler(func=lambda call: call.data == "sessions_status")
def sessions_status(call):
    if call.from_user.id != ADMIN_ID: return
    ss = session_manager.get_status(); tc = session_manager.stats['checks_total']; fc = session_manager.stats['checks_free']
    acc = round((fc/tc*100), 1) if tc else 0
    text = (f"<b><tg-emoji emoji-id='{E_SESSION_STATUS}'>📊</tg-emoji> Статус сессий</b>\n\n"
            f"<blockquote><b><tg-emoji emoji-id='{E_STATS_ACTIVE_SESS}'>🟢</tg-emoji> Активных: {ss['active']}</b>\n"
            f"<b><tg-emoji emoji-id='{E_STATS_WAITING}'>🟡</tg-emoji> Ожидают: {ss['waiting']}</b>\n"
            f"<b><tg-emoji emoji-id='{E_STATS_FLOOD}'>🔴</tg-emoji> В флуде: {ss['flood']}</b>\n"
            f"<b><tg-emoji emoji-id='{E_STATS_INVALID}'>⚫</tg-emoji> Невалид: {ss['invalid']}</b>\n"
            f"<b><tg-emoji emoji-id='{E_STATS_TOTAL_SESS}'>📱</tg-emoji> Всего: {ss['total']}</b>\n"
            f"<b><tg-emoji emoji-id='{E_STATS_CHECKS}'>🔍</tg-emoji> Проверок: {tc}</b>\n"
            f"<b><tg-emoji emoji-id='{E_STATS_ACCURACY}'>🎯</tg-emoji> Точность: {acc}%</b></blockquote>")
    markup = types.InlineKeyboardMarkup(); markup.add(btn("Назад", callback_data="admin_sessions", emoji=E_PROMO_BACK, style="primary"))
    safe_edit(call, text, markup)

@bot.callback_query_handler(func=lambda call: call.data == "sessions_delete")
def sessions_delete_list(call):
    if call.from_user.id != ADMIN_ID: return
    text = (f"<b><tg-emoji emoji-id='{E_SESSION_DELETE}'>🗑️</tg-emoji> Удалить сессии</b>\n\n"
            f"<b><tg-emoji emoji-id='{E_SESSION_DELETE_CHOOSE}'>📋</tg-emoji> Выбери кнопку ниже</b>")
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.add(btn("Активные", callback_data="sessions_del_active", emoji=E_SESSION_ACTIVE, style="primary"), btn("В флуде", callback_data="sessions_del_flood", emoji=E_SESSION_FLOOD, style="danger"),
               btn("Заблокированные", callback_data="sessions_del_invalid", emoji=E_STATS_BANNED, style="danger"), btn("Ожидающие", callback_data="sessions_del_waiting", emoji=E_SESSION_WAITING, style="primary"),
               btn("Удалить ВСЕ", callback_data="sessions_del_all", emoji=E_SESSION_DELETE, style="danger"), btn("Назад", callback_data="admin_sessions", emoji=E_PROMO_BACK, style="primary"))
    safe_edit(call, text, markup)

@bot.callback_query_handler(func=lambda call: call.data == "sessions_del_all")
def sessions_delete_all_confirm(call):
    if call.from_user.id != ADMIN_ID: return
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.add(btn("Да, удалить всё", callback_data="sessions_del_all_yes", emoji=E_WARN, style="danger"), btn("Отмена", callback_data="sessions_delete", emoji=E_WARN, style="danger"))
    safe_edit(call, f"<b><tg-emoji emoji-id='{E_WARN}'>⚠️</tg-emoji> Точно удалить ВСЕ сессии, включая ожидающие? Это необратимо.</b>", markup)

@bot.callback_query_handler(func=lambda call: call.data == "sessions_del_all_yes")
def sessions_delete_all_execute(call):
    if call.from_user.id != ADMIN_ID: return
    with session_manager.lock:
        to_remove = [s.id for s in session_manager.all_sessions[:]]
        for sid in to_remove: session_manager.remove_session(sid)
    bot.answer_callback_query(call.id, f"✅ Удалено {len(to_remove)} сессий", show_alert=True); sessions_delete_list(call)

@bot.callback_query_handler(func=lambda call: call.data.startswith("sessions_del_") and not call.data.startswith("sessions_del_all"))
def sessions_delete_confirm(call):
    if call.from_user.id != ADMIN_ID: return
    target = call.data.split("_")
    key = target[2]
    # 'invalid' и 'banned' — оба статуса нерабочих сессий, отображаются в UI одной кнопкой "Заблокированные",
    # поэтому при удалении должны совпадать оба, иначе banned/frozen сессии никогда не удаляются
    status_map = {"active": {"active"}, "flood": {"flood"}, "invalid": {"invalid", "banned"}, "waiting": {"waiting"}}
    if key in status_map:
        statuses = status_map[key]
    else:
        session_id = int(key); session_manager.remove_session(session_id); bot.answer_callback_query(call.id, "✅ Сессия удалена", show_alert=True); sessions_delete_list(call); return
    with session_manager.lock:
        to_remove = [s for s in session_manager.all_sessions[:] if s.status in statuses]
        for s in to_remove: session_manager.remove_session(s.id)
    bot.answer_callback_query(call.id, f"✅ Удалено {len(to_remove)} сессий", show_alert=True); sessions_delete_list(call)

@bot.callback_query_handler(func=lambda call: call.data == "sessions_reload")
def sessions_reload(call):
    if call.from_user.id != ADMIN_ID: return
    session_manager.load_from_db(); bot.answer_callback_query(call.id, "✅ Перезагружено", show_alert=True); admin_sessions_menu(call)

@bot.callback_query_handler(func=lambda call: call.data == "admin_upload_sessions_zip")
def admin_upload_sessions_zip_callback(call):
    if call.from_user.id != ADMIN_ID: return
    text = (f"<b><tg-emoji emoji-id='{E_WHAT}'>📦</tg-emoji> Загрузка сессий через</b>\n\n"
            f"<b><tg-emoji emoji-id='{E_CHOOSE}'>🎂</tg-emoji> Выберите раздел</b>")
    markup = types.InlineKeyboardMarkup(row_width=1)
    markup.add(btn("Через .zip", callback_data="zip_upload_start", emoji=E_SESSION_ADD_DESC, style="primary"), btn("Назад", callback_data="admin_back", emoji=E_PROMO_BACK, style="primary"))
    safe_edit(call, text, markup)

@bot.callback_query_handler(func=lambda call: call.data == "zip_upload_start")
def zip_upload_start_callback(call):
    if call.from_user.id != ADMIN_ID: return
    markup = types.InlineKeyboardMarkup(row_width=1); markup.add(btn("Отменить загрузку", callback_data="admin_back", emoji=E_WARN, style="danger"))
    bot.edit_message_text(f"<b><tg-emoji emoji-id='{E_WHAT}'>📦</tg-emoji> Отправьте ZIP-архив с файлами .session</b>\n\nДля отмены нажмите кнопку ниже.", call.message.chat.id, call.message.message_id, parse_mode='HTML', reply_markup=markup)
    bot.register_next_step_handler(call.message, process_zip_upload)

def process_zip_upload(message):
    if message.from_user.id != ADMIN_ID: return
    if message.text and message.text.lower() == 'отмена': bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Загрузка отменена", reply_markup=admin_inline_menu(), parse_mode='HTML'); return
    if not message.document or not message.document.file_name.endswith('.zip'): bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Отправьте ZIP-файл!", parse_mode='HTML'); return
    bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_WHAT}'>📦</tg-emoji> Обрабатываю архив...", parse_mode='HTML')
    try:
        file_info = bot.get_file(message.document.file_id); downloaded_file = bot.download_file(file_info.file_path)
        try: zip_file = zipfile.ZipFile(io.BytesIO(downloaded_file))
        except zipfile.BadZipFile: bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Архив поврежден!", parse_mode='HTML'); return
        session_files = [f for f in zip_file.namelist() if f.endswith('.session')]
        if not session_files: bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> В архиве нет .session файлов!", parse_mode='HTML'); zip_file.close(); return
        added_count = 0; temp_dir = 'temp_sessions_upload'; os.makedirs(temp_dir, exist_ok=True)
        for session_file in session_files:
            session_name = os.path.basename(session_file).replace('.session', '')
            with db_lock:
                cursor.execute("SELECT id FROM sessions WHERE phone=?", (session_name,))
                if cursor.fetchone(): continue
            zip_file.extract(session_file, temp_dir); session_path = os.path.join(temp_dir, session_file)
            try: session_string = run_async(extract_session_string(session_path))
            except: session_string = ""
            now = moscow_now().strftime('%Y-%m-%d %H:%M:%S')
            with db_lock: cursor.execute("INSERT INTO sessions (phone, session_string, status, created_at, updated_at) VALUES (?,?,'waiting',?,?)", (session_name, session_string, now, now)); conn.commit()
            added_count += 1
        zip_file.close(); shutil.rmtree(temp_dir, ignore_errors=True); session_manager.load_from_db()
        bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_FOUND_NICK}'>✅</tg-emoji> <b>ЗАГРУЗКА ЗАВЕРШЕНА</b>\n\n<tg-emoji emoji-id='{E_WHAT}'>📦</tg-emoji> Найдено: {len(session_files)}\n<tg-emoji emoji-id='{E_FOUND_NICK}'>✅</tg-emoji> Добавлено: {added_count}\n<tg-emoji emoji-id='{E_MAIN}'>⏳</tg-emoji> Статус: ожидают активации", parse_mode='HTML', reply_markup=admin_inline_menu())
    except Exception as e: bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Ошибка: {str(e)[:200]}", reply_markup=admin_inline_menu(), parse_mode='HTML')

async def extract_session_string(session_path):
    client = TelegramClient(session_path, API_ID, API_HASH); await client.connect()
    session_string = StringSession.save(client.session) if await client.is_user_authorized() else ""; await client.disconnect(); return session_string

_broadcast_drafts = {}

@bot.callback_query_handler(func=lambda call: call.data == "admin_broadcast")
def admin_broadcast_callback(call):
    if call.from_user.id != ADMIN_ID: return
    text = (f"<b><tg-emoji emoji-id='{E_BROADCAST}'>📢</tg-emoji> Рассылка по боту</b>\n\n"
            f"<b><tg-emoji emoji-id='{E_BROADCAST_DESC}'>📝</tg-emoji> Можно добавлять премиум эмодзи в текст.</b>\n\n"
            f"<b><tg-emoji emoji-id='{E_BROADCAST_CHOOSE}'>📋</tg-emoji> Выбери кнопку ниже:</b>")
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.add(btn("С кнопкой", callback_data="broadcast_type_button", emoji=E_CLICKABLE, style="primary"), btn("Просто текст", callback_data="broadcast_type_text", emoji=E_INFO_LIST, style="primary"),
               btn("Фото + кнопка", callback_data="broadcast_type_photo_button", emoji=E_CLICKABLE, style="primary"), btn("С фото", callback_data="broadcast_type_photo", emoji=E_INFO_LIST, style="primary"),
               btn("Назад", callback_data="admin_back", emoji=E_PROMO_BACK, style="primary"))
    safe_edit(call, text, markup)

@bot.callback_query_handler(func=lambda call: call.data.startswith("broadcast_type_"))
def broadcast_type_callback(call):
    if call.from_user.id != ADMIN_ID: return
    btype = call.data.split("_")[2]
    markup = types.InlineKeyboardMarkup(row_width=1); markup.add(btn("Отменить", callback_data="admin_back", emoji=E_WARN, style="danger"))
    if btype == "text": msg = bot.edit_message_text(f"<tg-emoji emoji-id='{E_BROADCAST}'>📢</tg-emoji> Введите текст рассылки:", call.message.chat.id, call.message.message_id, reply_markup=markup, parse_mode='HTML'); bot.register_next_step_handler(msg, broadcast_step, None, None)
    elif btype == "button": msg = bot.edit_message_text(f"<tg-emoji emoji-id='{E_BROADCAST}'>📢</tg-emoji> Введите текст рассылки:", call.message.chat.id, call.message.message_id, reply_markup=markup, parse_mode='HTML'); bot.register_next_step_handler(msg, broadcast_get_button_text)
    elif btype == "photo": msg = bot.edit_message_text(f"<tg-emoji emoji-id='{E_BROADCAST}'>📢</tg-emoji> Отправьте фото для рассылки:", call.message.chat.id, call.message.message_id, reply_markup=markup, parse_mode='HTML'); bot.register_next_step_handler(msg, broadcast_get_photo)
    elif btype == "photo_button": msg = bot.edit_message_text(f"<tg-emoji emoji-id='{E_BROADCAST}'>📢</tg-emoji> Отправьте фото для рассылки:", call.message.chat.id, call.message.message_id, reply_markup=markup, parse_mode='HTML'); bot.register_next_step_handler(msg, broadcast_get_photo_button)

def broadcast_get_button_text(message):
    if message.from_user.id != ADMIN_ID: return
    if not message.text: return
    text = message.html_text; msg = bot.send_message(message.chat.id, "🔘 Введите текст на кнопке:"); bot.register_next_step_handler(msg, broadcast_get_button_url, text)

def broadcast_get_button_url(message, broadcast_text):
    if message.from_user.id != ADMIN_ID: return
    if not message.text: return
    button_text = message.text; msg = bot.send_message(message.chat.id, "🌐 Введите ссылку для кнопки:"); bot.register_next_step_handler(msg, broadcast_with_button_step, broadcast_text, button_text)

def broadcast_with_button_step(message, broadcast_text, button_text):
    if message.from_user.id != ADMIN_ID: return
    if not message.text: return
    button_url = message.text.strip(); markup = types.InlineKeyboardMarkup(); markup.add(btn(button_text, url=button_url, style="primary"))
    confirm_broadcast(message.chat.id, broadcast_text, markup)

def broadcast_get_photo(message):
    if message.from_user.id != ADMIN_ID: return
    if message.text and message.text.lower() == 'отмена': bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Отменено", reply_markup=admin_inline_menu(), parse_mode='HTML'); return
    if not message.photo: bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Отправьте фото!", parse_mode='HTML'); return
    photo_id = message.photo[-1].file_id; msg = bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_BROADCAST}'>📢</tg-emoji> Введите текст рассылки:", parse_mode='HTML'); bot.register_next_step_handler(msg, broadcast_step, photo_id, None)

def broadcast_get_photo_button(message):
    if message.from_user.id != ADMIN_ID: return
    if message.text and message.text.lower() == 'отмена': bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Отменено", reply_markup=admin_inline_menu(), parse_mode='HTML'); return
    if not message.photo: bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Отправьте фото!", parse_mode='HTML'); return
    photo_id = message.photo[-1].file_id; msg = bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_BROADCAST}'>📢</tg-emoji> Введите текст рассылки:", parse_mode='HTML'); bot.register_next_step_handler(msg, broadcast_get_photo_button_text, photo_id)

def broadcast_get_photo_button_text(message, photo_id):
    if message.from_user.id != ADMIN_ID: return
    if not message.text: return
    text = message.html_text; msg = bot.send_message(message.chat.id, "🔘 Введите текст на кнопке:"); bot.register_next_step_handler(msg, broadcast_get_photo_button_url, photo_id, text)

def broadcast_get_photo_button_url(message, photo_id, broadcast_text):
    if message.from_user.id != ADMIN_ID: return
    if not message.text: return
    button_text = message.text; msg = bot.send_message(message.chat.id, "🌐 Введите ссылку для кнопки:"); bot.register_next_step_handler(msg, broadcast_photo_button_final, photo_id, broadcast_text, button_text)

def broadcast_photo_button_final(message, photo_id, broadcast_text, button_text):
    if message.from_user.id != ADMIN_ID: return
    if not message.text: return
    button_url = message.text.strip(); markup = types.InlineKeyboardMarkup(); markup.add(btn(button_text, url=button_url, style="primary"))
    confirm_broadcast(message.chat.id, broadcast_text, markup, photo_id)

def broadcast_step(message, photo_id=None, reply_markup=None):
    if message.from_user.id != ADMIN_ID: return
    if message.text and message.text.strip().lower() == 'отмена': bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Отменено", reply_markup=admin_inline_menu(), parse_mode='HTML'); return
    if not message.text: return
    confirm_broadcast(message.chat.id, message.html_text, reply_markup, photo_id)

def confirm_broadcast(chat_id, text, reply_markup=None, photo_id=None):
    # Показываем админу, как ровно будет выглядеть рассылка (включая премиум-эмодзи,
    # если они были вставлены в текст), и просим подтвердить отправку всем пользователям.
    try:
        if photo_id: bot.send_photo(chat_id, photo_id, caption=text, parse_mode='HTML', reply_markup=reply_markup)
        else: bot.send_message(chat_id, text, parse_mode='HTML', reply_markup=reply_markup)
    except Exception as e:
        bot.send_message(chat_id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Не удалось построить превью — проверьте текст/HTML-разметку.\n<code>{html_entities.escape(str(e))}</code>", reply_markup=admin_inline_menu(), parse_mode='HTML')
        return
    _broadcast_drafts[chat_id] = {'text': text, 'reply_markup': reply_markup, 'photo_id': photo_id}
    confirm_markup = types.InlineKeyboardMarkup(row_width=2)
    confirm_markup.add(btn("Да, разослать", callback_data="broadcast_confirm_yes", emoji=E_FOUND_NICK, style="success"),
                        btn("Нет, отменить", callback_data="broadcast_confirm_no", emoji=E_WARN, style="danger"))
    bot.send_message(chat_id, f"<tg-emoji emoji-id='{E_BROADCAST_CHOOSE}'>📋</tg-emoji> Выше показано, как сообщение увидят пользователи.\n\n<b>Разослать это сообщение всем пользователям?</b>", parse_mode='HTML', reply_markup=confirm_markup)

@bot.callback_query_handler(func=lambda call: call.data == "broadcast_confirm_yes")
def broadcast_confirm_yes_callback(call):
    if call.from_user.id != ADMIN_ID: return
    bot.answer_callback_query(call.id)
    draft = _broadcast_drafts.pop(call.message.chat.id, None)
    if not draft:
        bot.send_message(call.message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Черновик рассылки не найден (истёк или уже отправлен). Начните заново.", reply_markup=admin_inline_menu(), parse_mode='HTML'); return
    start_broadcast(call.message.chat.id, draft['text'], draft['reply_markup'], draft['photo_id'])

@bot.callback_query_handler(func=lambda call: call.data == "broadcast_confirm_no")
def broadcast_confirm_no_callback(call):
    if call.from_user.id != ADMIN_ID: return
    bot.answer_callback_query(call.id)
    _broadcast_drafts.pop(call.message.chat.id, None)
    bot.send_message(call.message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Рассылка отменена", reply_markup=admin_inline_menu(), parse_mode='HTML')

def start_broadcast(chat_id, text, reply_markup=None, photo_id=None):
    with db_lock: cursor.execute("SELECT user_id FROM users WHERE banned=0"); users = cursor.fetchall()
    if not users: bot.send_message(chat_id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Нет пользователей!", reply_markup=admin_inline_menu(), parse_mode='HTML'); return
    total = len(users); success = 0
    for user_id, in users:
        try:
            if photo_id: bot.send_photo(user_id, photo_id, caption=text, parse_mode='HTML', reply_markup=reply_markup)
            else: bot.send_message(user_id, text, parse_mode='HTML', reply_markup=reply_markup)
            success += 1
        except: pass
        time.sleep(0.05)
    bot.send_message(chat_id, f"<tg-emoji emoji-id='{E_FOUND_NICK}'>✅</tg-emoji> Рассылка завершена\n<tg-emoji emoji-id='{E_STATS_TOTAL}'>👥</tg-emoji> {total}\n<tg-emoji emoji-id='{E_FOUND_NICK}'>✅</tg-emoji> {success}", reply_markup=admin_inline_menu(), parse_mode='HTML')

@bot.callback_query_handler(func=lambda call: call.data == "admin_ban")
def admin_ban_callback(call):
    if call.from_user.id != ADMIN_ID: return
    msg = bot.send_message(call.message.chat.id, f"<tg-emoji emoji-id='{E_BANNED}'>🚫</tg-emoji> Введите ID для бана:", parse_mode='HTML'); bot.register_next_step_handler(msg, process_ban)

def process_ban(message):
    if message.from_user.id != ADMIN_ID: return
    if not message.text: return
    try: uid = int(message.text.strip()); update_user(uid, banned=1); bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_BANNED}'>🚫</tg-emoji> ID {uid} забанен", reply_markup=admin_inline_menu(), parse_mode='HTML')
    except ValueError: bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Введите число!", reply_markup=admin_inline_menu(), parse_mode='HTML')

@bot.callback_query_handler(func=lambda call: call.data == "admin_unban")
def admin_unban_callback(call):
    if call.from_user.id != ADMIN_ID: return
    msg = bot.send_message(call.message.chat.id, f"<tg-emoji emoji-id='{E_FOUND_NICK}'>✅</tg-emoji> Введите ID для разбана:", parse_mode='HTML'); bot.register_next_step_handler(msg, process_unban)

def process_unban(message):
    if message.from_user.id != ADMIN_ID: return
    if not message.text: return
    try: uid = int(message.text.strip()); update_user(uid, banned=0); bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_FOUND_NICK}'>✅</tg-emoji> ID {uid} разбанен", reply_markup=admin_inline_menu(), parse_mode='HTML')
    except ValueError: bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Введите число!", reply_markup=admin_inline_menu(), parse_mode='HTML')

@bot.callback_query_handler(func=lambda call: call.data == "admin_premium")
def admin_premium_callback(call):
    if call.from_user.id != ADMIN_ID: return
    text = f"<b><tg-emoji emoji-id='{E_PREMIUM}'>⭐</tg-emoji> Управление премиумом</b>\n\nВыберите способ:"
    markup = types.InlineKeyboardMarkup(row_width=1)
    markup.add(btn("По ID", callback_data="premium_give_id", emoji=E_ID_LABEL, style="primary"),
               btn("По Username", callback_data="premium_give", emoji=E_USERNAME_LABEL, style="primary"),
               btn("Забрать премиум", callback_data="premium_take", emoji=E_WARN, style="danger"),
               btn("Назад", callback_data="admin_back", emoji=E_PROMO_BACK, style="primary"))
    safe_edit(call, text, markup)

@bot.callback_query_handler(func=lambda call: call.data == "premium_give_id")
def premium_give_id_callback(call):
    if call.from_user.id != ADMIN_ID: return
    msg = bot.send_message(call.message.chat.id, "Введите ID пользователя:")
    bot.register_next_step_handler(msg, process_premium_give_id)

def process_premium_give_id(message):
    if message.from_user.id != ADMIN_ID: return
    if not message.text: return
    try:
        user_id = int(message.text.strip())
    except ValueError:
        bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Введите число!", reply_markup=admin_inline_menu(), parse_mode='HTML'); return
    user = get_user_by_id(user_id)
    if not user:
        bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Пользователь с ID {user_id} не найден", reply_markup=admin_inline_menu(), parse_mode='HTML'); return
    msg = bot.send_message(message.chat.id, f"Введите количество дней премиума для ID {user_id}:")
    bot.register_next_step_handler(msg, process_premium_give_days, user_id)

@bot.callback_query_handler(func=lambda call: call.data == "premium_give")
def premium_give_callback(call):
    if call.from_user.id != ADMIN_ID: return
    msg = bot.send_message(call.message.chat.id, "Введите юзернейм пользователя (без @):")
    bot.register_next_step_handler(msg, process_premium_give_username)

def process_premium_give_username(message):
    if message.from_user.id != ADMIN_ID: return
    if not message.text: return
    username = message.text.strip().replace('@', '')
    user_id = get_user_by_username(username)
    if not user_id:
        bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Пользователь @{username} не найден", reply_markup=admin_inline_menu(), parse_mode='HTML'); return
    msg = bot.send_message(message.chat.id, f"Введите количество дней премиума для @{username}:")
    bot.register_next_step_handler(msg, process_premium_give_days, user_id)

def process_premium_give_days(message, user_id):
    if message.from_user.id != ADMIN_ID: return
    if not message.text: return
    try:
        days = int(message.text.strip())
        if days <= 0: raise ValueError
    except ValueError:
        bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Введите число больше 0!", reply_markup=admin_inline_menu(), parse_mode='HTML'); return
    user = get_user(user_id)
    current_expires = user.get('premium_expires')
    if current_expires:
        try:
            exp_dt = datetime.datetime.strptime(current_expires, '%Y-%m-%d %H:%M:%S').replace(tzinfo=MOSCOW_TZ)
            if exp_dt > moscow_now():
                new_expires = exp_dt + datetime.timedelta(days=days)
            else:
                new_expires = moscow_now() + datetime.timedelta(days=days)
        except:
            new_expires = moscow_now() + datetime.timedelta(days=days)
    else:
        new_expires = moscow_now() + datetime.timedelta(days=days)
    update_user(user_id, is_premium=1, premium_expires=new_expires.strftime('%Y-%m-%d %H:%M:%S'), premium_source='admin')
    bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_FOUND_NICK}'>✅</tg-emoji> Премиум для ID {user_id} выдан на {days} дней. Истекает: {new_expires.strftime('%d.%m.%Y %H:%M')}", reply_markup=admin_inline_menu(), parse_mode='HTML')
    try:
        bot.send_message(user_id, f"<b><tg-emoji emoji-id='{E_PREMIUM}'>⭐</tg-emoji> Вам выдан премиум на {days} дней!</b>", parse_mode='HTML')
    except: pass

@bot.callback_query_handler(func=lambda call: call.data == "premium_take")
def premium_take_callback(call):
    if call.from_user.id != ADMIN_ID: return
    msg = bot.send_message(call.message.chat.id, "Введите ID или юзернейм пользователя:")
    bot.register_next_step_handler(msg, process_premium_take_username)

def process_premium_take_username(message):
    if message.from_user.id != ADMIN_ID: return
    if not message.text: return
    input_text = message.text.strip()
    user_id = None
    if input_text.isdigit():
        user_id = int(input_text)
    else:
        user_id = get_user_by_username(input_text.replace('@', ''))
    if not user_id:
        bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Пользователь {input_text} не найден", reply_markup=admin_inline_menu(), parse_mode='HTML'); return
    update_user(user_id, is_premium=0, premium_expires=None, premium_source=None)
    bot.send_message(message.chat.id, f"<tg-emoji emoji-id='{E_FOUND_NICK}'>✅</tg-emoji> Премиум у ID {user_id} забран", reply_markup=admin_inline_menu(), parse_mode='HTML')
    try:
        bot.send_message(user_id, f"<b><tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Ваш премиум был отозван.</b>", parse_mode='HTML')
    except: pass

# ==================== ПРОМОКОДЫ ====================

def promo_admin_markup():
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.add(
        btn("Создать промокод", callback_data="promo_create", emoji=E_PROMO_GIFT, style="success"),
        btn("Список промокодов", callback_data="promo_list", emoji=E_PROMO_PANEL, style="primary"),
        btn("Удалить промокод", callback_data="promo_delete", emoji=E_WARN, style="danger"),
        btn("Назад", callback_data="admin_back", emoji=E_PROMO_BACK, style="primary")
    )
    return markup

def promo_status_text():
    with db_lock:
        cursor.execute("SELECT COUNT(*), COALESCE(SUM(activations_count),0) FROM promocodes")
        cnt, total_act = cursor.fetchone()
    return (f"<b><tg-emoji emoji-id='{E_PROMO_PANEL}'>🎛</tg-emoji> Промокоды</b>\n\n"
            f"<blockquote><b>Всего создано:</b> {cnt}\n"
            f"<b>Всего активаций:</b> {total_act}</blockquote>\n\n"
            f"<i>Создай промокод на N активаций и M дней премиума, посмотри список действующих кодов или удали ненужный.</i>")

@bot.callback_query_handler(func=lambda call: call.data == "admin_promo")
def admin_promo_callback(call):
    if call.from_user.id != ADMIN_ID: return
    bot.answer_callback_query(call.id)
    try:
        safe_edit(call, promo_status_text(), promo_admin_markup())
    except Exception as e:
        logger.error(f"admin_promo_callback: {e}")
        try: bot.send_message(call.message.chat.id, "Промокоды", reply_markup=promo_admin_markup())
        except: pass

def _generate_promo_code(length=8):
    import string
    alphabet = string.ascii_uppercase + string.digits
    while True:
        code = ''.join(random.choice(alphabet) for _ in range(length))
        with db_lock:
            cursor.execute("SELECT 1 FROM promocodes WHERE code=?", (code,))
            if not cursor.fetchone(): return code

@bot.callback_query_handler(func=lambda call: call.data == "promo_create")
def promo_create_callback(call):
    if call.from_user.id != ADMIN_ID: return
    bot.answer_callback_query(call.id)
    msg = send_html_safe(call.message.chat.id,
        f"<tg-emoji emoji-id='{E_PROMO_TAG}'>🔖</tg-emoji> Введите текст промокода (например, <code>NEWYEAR2026</code>), либо напишите «авто» — сгенерирую случайный.\n\nДля отмены напишите «отмена».")
    if msg: bot.register_next_step_handler(msg, process_promo_code)

def process_promo_code(message):
    if message.from_user.id != ADMIN_ID: return
    if not message.text: return
    raw = message.text.strip()
    if raw.lower() == 'отмена':
        send_html_safe(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Отменено", reply_markup=promo_admin_markup()); return
    if raw.lower() == 'авто':
        code = _generate_promo_code()
    else:
        code = re.sub(r'\s+', '', raw).upper()
        if not code or len(code) > 32:
            msg = send_html_safe(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Некорректный промокод (1-32 символа, без пробелов). Введите ещё раз:")
            if msg: bot.register_next_step_handler(msg, process_promo_code)
            return
        with db_lock:
            cursor.execute("SELECT 1 FROM promocodes WHERE code=?", (code,))
            exists = cursor.fetchone()
        if exists:
            msg = send_html_safe(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Промокод <code>{code}</code> уже существует. Введите другой:")
            if msg: bot.register_next_step_handler(msg, process_promo_code)
            return
    msg = send_html_safe(message.chat.id,
        f"<tg-emoji emoji-id='{E_PROMO_GIFT}'>🎁</tg-emoji> Сколько пользователей смогут активировать промокод <code>{code}</code>?\n\nВведите число:")
    if msg: bot.register_next_step_handler(msg, process_promo_activations, code)

def process_promo_activations(message, code):
    if message.from_user.id != ADMIN_ID: return
    if not message.text: return
    if message.text.strip().lower() == 'отмена':
        send_html_safe(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Отменено", reply_markup=promo_admin_markup()); return
    try:
        max_act = int(message.text.strip())
        if max_act <= 0: raise ValueError
    except ValueError:
        msg = send_html_safe(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Введите целое число больше 0!")
        if msg: bot.register_next_step_handler(msg, process_promo_activations, code)
        return
    msg = send_html_safe(message.chat.id,
        f"<tg-emoji emoji-id='{E_PROMO_STAR}'>⭐</tg-emoji> На сколько дней премиума будет действовать промокод <code>{code}</code>?\n\nВведите число:")
    if msg: bot.register_next_step_handler(msg, process_promo_days, code, max_act)

def process_promo_days(message, code, max_act):
    if message.from_user.id != ADMIN_ID: return
    if not message.text: return
    if message.text.strip().lower() == 'отмена':
        send_html_safe(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Отменено", reply_markup=promo_admin_markup()); return
    try:
        days = int(message.text.strip())
        if days <= 0: raise ValueError
    except ValueError:
        msg = send_html_safe(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Введите целое число больше 0!")
        if msg: bot.register_next_step_handler(msg, process_promo_days, code, max_act)
        return
    now_str = moscow_now().strftime('%Y-%m-%d %H:%M:%S')
    with db_lock:
        cursor.execute("INSERT INTO promocodes (code, days, max_activations, activations_count, created_by, created_at, active) VALUES (?,?,?,0,?,?,1)",
                        (code, days, max_act, message.from_user.id, now_str))
        conn.commit()
    bot_username = bot.get_me().username or "bot"
    text = (f"<b><tg-emoji emoji-id='{E_PROMO_OK}'>✔️</tg-emoji> Промокод успешно создан!</b>\n\n"
            f"<blockquote><b><tg-emoji emoji-id='{E_PROMO_TAG}'>🔖</tg-emoji> Промокод:</b> <code>{code}</code>\n"
            f"<b><tg-emoji emoji-id='{E_PROMO_STAR}'>⭐</tg-emoji> Премиум:</b> {days} дн.\n"
            f"<b><tg-emoji emoji-id='{E_PROMO_GIFT}'>🎁</tg-emoji> Активаций:</b> 0/{max_act}</blockquote>\n\n"
            f"<b><tg-emoji emoji-id='{E_PROMO_PIC}'>🖼</tg-emoji> Как активировать пользователю:</b>\n"
            f"<blockquote><b>1.</b> Открыть раздел <b>«Профиль»</b>\n"
            f"<b>2.</b> Нажать кнопку <b>«Промокод»</b>\n"
            f"<b>3.</b> Отправить код <code>{code}</code> сообщением в чат</blockquote>\n\n"
            f"<b>Активировать в боте:</b> @{bot_username}")
    send_html_safe(message.chat.id, text, reply_markup=promo_admin_markup())

@bot.callback_query_handler(func=lambda call: call.data == "promo_list")
def promo_list_callback(call):
    if call.from_user.id != ADMIN_ID: return
    bot.answer_callback_query(call.id)
    with db_lock:
        cursor.execute("SELECT code, days, max_activations, activations_count, active FROM promocodes ORDER BY created_at DESC LIMIT 30")
        rows = cursor.fetchall()
    if not rows:
        text = f"<b><tg-emoji emoji-id='{E_PROMO_PANEL}'>🎛</tg-emoji> Список промокодов</b>\n\n<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Промокодов пока нет"
    else:
        text = f"<b><tg-emoji emoji-id='{E_PROMO_PANEL}'>🎛</tg-emoji> Список промокодов</b>\n\n<blockquote>"
        for code, days, max_act, used, active in rows:
            is_alive = active and used < max_act
            mark = f"<tg-emoji emoji-id='{E_PROMO_OK}'>✔️</tg-emoji>" if is_alive else f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji>"
            text += f"{mark} <code>{code}</code> — {days} дн. — {used}/{max_act}\n"
        text += "</blockquote>"
    markup = types.InlineKeyboardMarkup(); markup.add(btn("Назад", callback_data="admin_promo", emoji=E_PROMO_BACK, style="primary"))
    safe_edit(call, text, markup)

@bot.callback_query_handler(func=lambda call: call.data == "promo_delete")
def promo_delete_callback(call):
    if call.from_user.id != ADMIN_ID: return
    bot.answer_callback_query(call.id)
    msg = send_html_safe(call.message.chat.id, f"<tg-emoji emoji-id='{E_PROMO_TAG}'>🔖</tg-emoji> Введите код промокода для удаления:\n\nДля отмены напишите «отмена».")
    if msg: bot.register_next_step_handler(msg, process_promo_delete)

def process_promo_delete(message):
    if message.from_user.id != ADMIN_ID: return
    if not message.text: return
    if message.text.strip().lower() == 'отмена':
        send_html_safe(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Отменено", reply_markup=promo_admin_markup()); return
    code = re.sub(r'\s+', '', message.text.strip()).upper()
    with db_lock:
        cursor.execute("SELECT 1 FROM promocodes WHERE code=?", (code,))
        exists = cursor.fetchone()
        if exists:
            cursor.execute("DELETE FROM promocodes WHERE code=?", (code,))
            cursor.execute("DELETE FROM promo_activations WHERE code=?", (code,))
            conn.commit()
    if exists:
        send_html_safe(message.chat.id, f"<tg-emoji emoji-id='{E_PROMO_OK}'>✔️</tg-emoji> Промокод <code>{code}</code> удалён", reply_markup=promo_admin_markup())
    else:
        send_html_safe(message.chat.id, f"<tg-emoji emoji-id='{E_WARN}'>❌</tg-emoji> Промокод <code>{code}</code> не найден", reply_markup=promo_admin_markup())

@bot.message_handler(func=lambda message: message.text and message.text.strip().lower() == "поддержать проект")
def support_project_handler(message):
    bot.send_message(message.chat.id, "<b>Интерфейс обновлён. Пожалуйста нажмите /start.</b>", parse_mode='HTML')

@bot.message_handler(func=lambda message: True)
def unknown_command(message):
    if message.from_user.id == ADMIN_ID: return
    bot.send_message(message.chat.id, "<b>Используйте кнопки меню для навигации.</b>", parse_mode='HTML')

def schedule_midnight_report():
    while True:
        try:
            now = moscow_now(); next_midnight = (now + datetime.timedelta(days=1)).replace(hour=0, minute=0, second=0, microsecond=0)
            sleep_seconds = (next_midnight - now).total_seconds()
            if sleep_seconds > 0: time.sleep(sleep_seconds)
            reset_daily_stats_if_new_day()
            yesterday_dt = moscow_now() - datetime.timedelta(days=1)
            report_date = yesterday_dt.strftime('%d.%m.%Y'); yesterday = yesterday_dt.strftime('%Y-%m-%d')
            with db_lock:
                cursor.execute("SELECT new_users, new_refs, found_nicks, rejected_nicks FROM daily_stats WHERE date = ?", (yesterday,))
                row = cursor.fetchone()
                if row: new_users, new_refs, found_today, rejected = row
                else: new_users = new_refs = found_today = rejected = 0
            report_text = (f"<b><tg-emoji emoji-id='{E_ADMIN_REPORT}'>📊</tg-emoji> Отчёт за {report_date}</b>\n\n"
                          f"<blockquote><b><tg-emoji emoji-id='{E_ADMIN_NEW_USERS}'>👥</tg-emoji> Новых людей: {new_users}</b>\n"
                          f"<b><tg-emoji emoji-id='{E_ADMIN_NEW_REF}'>🔗</tg-emoji> Новых с реф. ссылки: {new_refs}</b>\n"
                          f"<b><tg-emoji emoji-id='{E_ADMIN_FOUND_NICKS}'>✅</tg-emoji> Найдено ников: {found_today}</b></blockquote>\n\n"
                          f"<i>Счётчики обнулены. Новый день начался.</i>")
            try: bot.send_message(ADMIN_ID, report_text, parse_mode='HTML')
            except: pass
        except: time.sleep(60)

threading.Thread(target=schedule_midnight_report, daemon=True).start()

def schedule_username_update():
    while True:
        time.sleep(3600)
        try: update_all_usernames()
        except: pass

threading.Thread(target=schedule_username_update, daemon=True).start()

PROMO_USERNAME_CHECK_THROTTLE = 10  # сек — не чаще раза в это время на пользователя

_last_promo_username_check = {}
_last_promo_username_check_lock = threading.Lock()

def _maybe_check_promo_username(user_id):
    """Проверяет юзернейм бота в имени профиля для премиума, полученного по промокоду
    (premium_source='promo'), но только когда пользователь сам взаимодействует с ботом
    (сообщение/колбэк) — не чаще раза в PROMO_USERNAME_CHECK_THROTTLE секунд на
    пользователя. Если пользователь ботом не пользуется — проверка не запускается и
    уведомление не шлётся. Купленный/выданный админом премиум не проверяется —
    юзернейм для него не обязателен."""
    now_ts = time.time()
    with _last_promo_username_check_lock:
        last = _last_promo_username_check.get(user_id, 0)
        if now_ts - last < PROMO_USERNAME_CHECK_THROTTLE:
            return
        _last_promo_username_check[user_id] = now_ts
    user = get_user(user_id)
    if not user or user.get('premium_source') != 'promo':
        logger.info(f"promo_username_check[{user_id}]: source={user.get('premium_source') if user else None} — пропуск")
        return
    expires = user.get('premium_expires')
    if not expires:
        logger.info(f"promo_username_check[{user_id}]: нет premium_expires — пропуск")
        return
    try:
        exp_dt = datetime.datetime.strptime(expires, '%Y-%m-%d %H:%M:%S').replace(tzinfo=MOSCOW_TZ)
    except Exception:
        logger.info(f"promo_username_check[{user_id}]: не смог распарсить expires={expires} — пропуск")
        return
    if exp_dt <= moscow_now():
        logger.info(f"promo_username_check[{user_id}]: срок уже истёк ({expires}) — пропуск")
        return
    try:
        has_name = _bot_username_in_name(user_id)
    except Exception as e:
        logger.warning(f"promo_username_check[{user_id}]: ошибка _bot_username_in_name: {e}")
        return
    is_premium = user.get('is_premium', 0)
    logger.info(f"promo_username_check[{user_id}]: has_name={has_name}, is_premium={is_premium}, expires={expires}")
    if not has_name and is_premium == 1:
        update_user(user_id, is_premium=0)
        try:
            bot.send_message(user_id,
                f"<b><tg-emoji emoji-id='{E_WARN}'>⚠️</tg-emoji> Премиум временно отключён.</b>\n\n"
                f"<blockquote>Ты убрал юзернейм бота из имени профиля. Премиум, полученный по промокоду, "
                f"работает только пока юзернейм бота указан в имени. Верни его в имя, чтобы снова включить "
                f"премиум — срок при этом не сбрасывается и продолжает идти.</blockquote>",
                parse_mode='HTML')
        except Exception as e:
            logger.warning(f"promo_username_check[{user_id}]: не смог отправить уведомление об отключении: {e}")
    elif has_name and is_premium == 0:
        update_user(user_id, is_premium=1)
        try:
            bot.send_message(user_id,
                f"<b><tg-emoji emoji-id='{E_FOUND_NICK}'>✅</tg-emoji> Премиум снова активен!</b>\n\n"
                f"<blockquote>Юзернейм бота найден в имени профиля — премиум включён обратно.</blockquote>",
                parse_mode='HTML')
        except Exception as e:
            logger.warning(f"promo_username_check[{user_id}]: не смог отправить уведомление о включении: {e}")

def _scan_promo_premium_usernames():
    """Проходит по всем пользователям с активным премиумом от промокода и для каждого
    вызывает _maybe_check_promo_username. Работает в отдельном фоновом потоке и никак
    не завязана на обработку сообщений/колбэков ботом — не может повлиять на остальную
    логику бота."""
    now_str = moscow_now().strftime('%Y-%m-%d %H:%M:%S')
    with db_lock:
        cursor.execute("SELECT user_id FROM users WHERE premium_source='promo' AND premium_expires IS NOT NULL AND premium_expires > ?", (now_str,))
        user_ids = [row[0] for row in cursor.fetchall()]
    for user_id in user_ids:
        try:
            _maybe_check_promo_username(user_id)
        except Exception as e:
            logger.warning(f"_scan_promo_premium_usernames[{user_id}]: {e}")

def schedule_promo_premium_check():
    while True:
        time.sleep(PROMO_USERNAME_CHECK_THROTTLE)
        try: _scan_promo_premium_usernames()
        except Exception as e: logger.warning(f"schedule_promo_premium_check: {e}")

threading.Thread(target=schedule_promo_premium_check, daemon=True).start()

if __name__ == '__main__':
    try:
        while True:
            try:
                bot.polling(none_stop=True, interval=0, timeout=20)
            except Exception as e:
                logger.error(f"Polling error: {e}")
                time.sleep(3)
    except KeyboardInterrupt:
        logger.info("Bot stopped by user")
        conn.close()