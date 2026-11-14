// ==UserScript==
// @name         Argon Survey Guard v13.5 (Access Control + Quiet Mode)
// @namespace    http://tampermonkey.net/
// !!! NEVER CHANGE @name OR @namespace AGAIN. Tampermonkey ties the saved data (Access ID, name, locks) to them.
// !!! A new @name = a NEW script = NEW Access ID + empty storage. Only change @version.
// @version      14.5
// @updateURL    https://raw.githubusercontent.com/rohimgpt/argon-script/main/argon.user.js
// @downloadURL  https://raw.githubusercontent.com/rohimgpt/argon-script/main/argon.user.js
// @description  Locks a completed survey for 7/15/30 days, tracks real start-to-end time, merge-able backups, admin-controlled remote blocklist (domains / keywords, also checked inside page links), and an approval system (Pending / Allowed / Blocked access IDs).
// @match        *://*/*
// @noframes
// @grant        GM_setValue
// @grant        GM_getValue
// @grant        GM_getTab
// @grant        GM_saveTab
// @grant        GM_registerMenuCommand
// @grant        GM_unregisterMenuCommand
// @grant        GM_notification
// @grant        GM_xmlhttpRequest
// @grant        GM_openInTab
// @connect      raw.githubusercontent.com
// @connect      api.github.com
// @connect      argon-track.mdsam7997.workers.dev
// @run-at       document-start
// ==/UserScript==
// SECURITY NOTE: network is used ONLY to (a) download the admin list (plain JSON data, never executed)
// (b) the manual "Check for update" menu item (reads the @version line of the script file only),
// (c) employee work report to your own server (client ID, employee name, access status, per survey: domain + duration; no full URLs / questions / answers), only if TRACK_URL is set (one report every 6 hours),
// and (d) for the admin only: publish changes to that JSON file via the GitHub API, and read the report data from your own server.
// No @require, no @resource, no eval.

(function () {
    'use strict';

    /* =====================================================================
     * CONFIG
     * ===================================================================== */
    const MIN = 60 * 1000, HOUR = 60 * MIN, DAY = 24 * HOUR;

    const LOCK_CHOICES = [7, 15, 30];              // admin buttons
    let LOCK_DAYS = 15;                            // changed by the admin list (applyLockDays)
    let LOCK_MS = LOCK_DAYS * DAY;
    const MAX_LOCK_MS = 30 * DAY;                  // locks are KEPT in storage up to 30 days, so switching 7 -> 30 days never loses data
    const LOG_KEEP_MS = 31 * DAY;
    const ACTIVE_TTL_MS = 3 * HOUR;
    const IDLE_MS = 45 * MIN;
    const ADOPT_MS = 5 * MIN;
    const HOST_GAP_MS = 10 * MIN;
    const DONE_MS = 5 * MIN;
    const FAST_MS = 12 * MIN;

    const MIN_QUESTIONS_FOR_FINAL = 3;
    const MIN_MATCHES = 3;
    const MIN_MATCH_PAGES = 2;
    const SINGLE_PAGE_MATCHES = 6;

    const MAX_KEYS = 400;
    const MAX_SIGNAL_TEXT = 3000;
    const MAX_FINGERPRINTS_PER_PAGE = 20;
    const MAX_QUESTION_CANDIDATES = 30;
    const MAX_FALLBACK_CONTROLS = 12;
    const INITIAL_PAGE_GRACE_MS = 15 * 1000;
    const IFRAME_MIN_W = 300, IFRAME_MIN_H = 300;   // only big iframes count (ads are ignored)

    const SCAN_DEBOUNCE_MS = 700;
    const MIN_SCAN_INTERVAL_MS = 1200;
    const POLL_MS = 2500;

    const DEBUG = false;

    // QUIET MODE (recommended): the script adds NOTHING to survey pages (no banner, no DOM element,
    // no title change). Messages go to the browser's own notification instead.
    // The only things ever drawn on a page are the red block screens (completed survey / admin block / blocked ID).
    const QUIET_MODE = true;

    // Green "New survey" pill shown for 10s when a FRESH survey is detected.
    const GREEN_BADGE = true;
    const GREEN_BADGE_MS = 10000;

    // SAME storage keys as v10.x / v11.x => old locks / sheet rows are kept
    const LOCKS_KEY = 'argon_v10_locks';
    const LOG_KEY = 'argon_v10_log';
    const ACTIVE_KEY = 'argon_v10_active';
    const LASTFINAL_KEY = 'argon_v10_lastfinal';
    const MUTEX_KEY = 'argon_v10_mutex';
    const BACKUP_KEY = 'argon_v10_backup_pre11';

    /* ---------- ADMIN BLOCKLIST CONFIG ---------- */
    // v14.4 REPO SPLIT: the SCRIPT lives in one repo, the admin DATA (blocklist / license lists) in another.
    // The GitHub token you paste in the admin menu must have access ONLY to the DATA repo (GH_REPO).
    // So if that token ever leaks, nobody can overwrite the script that runs in every employee's browser.
    // Both repos must be PUBLIC (raw.githubusercontent.com is read without a login).
    const GH_OWNER = 'rohimgpt';
    const GH_REPO = 'argon-data';                 // DATA repo  (contains argon-blocklist.json)  <- token goes here
    const GH_SCRIPT_REPO = 'argon-script';        // SCRIPT repo (contains argon.user.js)         <- NO token access
    const GH_PATH = 'argon-blocklist.json';
    const GH_BRANCH = 'main';
    const REMOTE_LIST_URL = 'https://raw.githubusercontent.com/' + GH_OWNER + '/' + GH_REPO + '/' + GH_BRANCH + '/' + GH_PATH;
    const REMOTE_REFRESH_MS = 5 * MIN;          // every user checks the list every ~5 min
    const ADMIN_KEY = 'argon_v11_admin_list';

    /* ---------- LINK SCAN (v13.4) ----------
     * The admin's domains / keywords are also matched against every <a href> inside the page.
     *  - a CLICK on a matching link is always stopped (left click, middle click, keyboard Enter)
     *  - if LINK_BLOCK_PAGE is true, a page that CONTAINS a matching link is blocked completely (strict mode)
     * Router / Lootwalls listing pages contain many survey links by design, so there the whole page is NOT blocked
     * (only the click is stopped) unless you set LINK_PAGE_BLOCK_ON_ROUTERS to true. */
    const LINK_BLOCK_PAGE = true;
    const LINK_PAGE_BLOCK_ON_ROUTERS = false;
    const LINK_SCAN_MAX = 500;

    /* ---------- ACCESS CONTROL (v13.4) ----------
     * Status of this browser's Access ID:  active = all features | pending = waiting for admin | blocked = admin blocked it.
     * Pending and Blocked IDs get NO guard feature at all (no repeat block, no admin domain block, no timer, no log).
     * They still send the 6-hourly report so the admin can see them. */
    const FAIL_CLOSED_NO_LIST = true;      // true: a browser that has never downloaded the admin list counts as Pending (closes the fresh-install gap)
    const BLOCKED_SCREEN = 'all';          // 'all' = red screen on every page for a Blocked ID | 'notify' = only a browser notification (at most every 10 min)

    /* ---------- USAGE REPORT (heartbeat) CONFIG ---------- */
    // Leave TRACK_URL empty ('') to switch the whole feature OFF (no network call at all).
    // >>> Replace YOURNAME (here and in the @connect line above) with your workers.dev subdomain <<<
    const TRACK_URL = 'https://argon-track.mdsam7997.workers.dev';
    const TRACK_INGEST_KEY = '0a47986d4c6ea4d469fcf6ad430c7d8befdf2f64d5a4ffe6';   // same value as INGEST_KEY secret in the worker (write-only key)
    const HEARTBEAT_MS = 6 * HOUR;         // one report per browser every 6 hours (all tabs share it)
    const TRACK_MAX_ROWS = 100;            // max survey records per report (the rest follows in the next one)
    const SYNC_KEY = 'argon_v13_sync';     // timestamp of the last survey record the server confirmed
    const HB_KEY = 'argon_v13_hb';         // only a timestamp is stored in the user's browser
    const NAME_SENT_KEY = 'argon_v13_name_sent';   // the name the server already has
    const NAME_ASKED_KEY = 'argon_v13_name_asked';
    const NAME_KEY = 'argon_v13_emp_name';   // employee name / ID typed by the employee once
    const NOTIFY_KEY = 'argon_v13_state_notify';   // timestamp of the last Pending / Blocked notification
    const TRACK_TOKEN_KEY = 'argon_v13_track_admin_token';   // read token: stays ONLY in the admin's own Tampermonkey storage
    const SCRIPT_URL = 'https://raw.githubusercontent.com/' + GH_OWNER + '/' + GH_SCRIPT_REPO + '/' + GH_BRANCH + '/argon.user.js';
    // Rules built into the script itself (always on, optional)
    const BUILTIN_BLOCK = { domains: [], keywords: [] };

    // Admin password is stored only as a salted SHA-256 hash (password itself is NOT in the code)
    // >>> CHANGE THIS HASH (see the step-by-step guide, step 3). Keep ADMIN_SALT as it is. <<<
    const ADMIN_PASS_HASH = 'efccd35ed9cc6f8cf4529d63bdcdd8c5138e695e97d96dea8e61dd5324267847';
    const ADMIN_SALT = 'argon-admin|';
    const ADMIN_SESSION_MS = 20 * MIN;
    const TOKEN_KEY = 'argon_v11_gh_token';        // GitHub token: stays ONLY in the admin's own Tampermonkey storage
    const CLIENT_ID_KEY = 'argon_v12_client_id';   // this browser's own license ID (auto-generated)
    const ADMIN_FAIL_KEY = 'argon_v11_admin_fail';

    function dbg() { if (DEBUG) console.log.apply(console, ['[Argon]'].concat([].slice.call(arguments))); }

    if (typeof GM_getValue !== 'function' || typeof GM_setValue !== 'function') {
        console.warn('[Argon] GM_getValue/GM_setValue not available. Use Tampermonkey.');
        return;
    }

    const host = location.hostname.toLowerCase();
    const hostIs = (d) => host === d || host.endsWith('.' + d);

    const NON_SURVEY_HOSTS = [
        'google.com', 'youtube.com', 'facebook.com', 'deepseek.com', 'openai.com',
        'chatgpt.com', 'claude.ai', 'bing.com', 'yahoo.com', 'reddit.com',
        'wikipedia.org', 'amazon.com', 'netflix.com', 'twitter.com', 'x.com',
        'instagram.com', 'github.com', 'linkedin.com', 'gmail.com', 'outlook.com',
        'localhost', '127.0.0.1'
    ];
    if (NON_SURVEY_HOSTS.some(hostIs)) return;

    const ROUTER_DOMAINS = [
        'samplicio.us', 'dtect.io', 'ovationworldpanel.com', 'dynata.com',
        'ssisurveys.com', 'cloudresearch.com', 'rdsecured.com', 'questmindshare.com',
        'kantar.com', 'navigatorsurveys.com', 'neuralbyt.com', 'trayistats.com',
        'samplecounts.com', 'sample-cube.com', 'opinionest.com', 'zamplia.com',
        'reachcollective.com', 'opinionelite.com', 'primeopinion.com', 'heycash.com',
        'earnstar.com', 'splitdrop.com', 'swagbucks.com', 'inboxdollars.com',
        'freecash.com', 'fivesurveys.com', 'topsurveys.app', 'surveyjunkie.com',
        'cpx-research.com', 'bitlabs.ai', 'tapresearch.com', 'theoremreach.com',
        'inbrain.ai', 'ayetstudios.com', 'revu.co', 'lootably.com'
    ];
    const hostInList = (h, list) => list.some(d => h === d || h.endsWith('.' + d));
    const isRouterDomain = hostInList(host, ROUTER_DOMAINS);
    const IS_UT = hostIs('usertesting.com');   // v14.4: UserTesting specific rules (one question per page, "N of N" progress bar)

    const NON_SURVEY_SEGMENTS = new Set([
        'login', 'signin', 'signup', 'register', 'account', 'profile', 'settings',
        'rewards', 'payments', 'withdraw', 'cashout', 'leaderboard', 'referrals',
        'support', 'help', 'faq', 'terms', 'privacy', 'activity', 'entry', 'router', 'profiler'
    ]);

    const PROJECT_PATTERNS = [
        { re: /\/selfserve\/([^\/]+\/[^\/?#]+)/i, prefix: 'id::decipher::' },
        { re: /\/(SV_[a-zA-Z0-9]+)/, prefix: 'id::qualtrics::' },
        { re: /\/(p\d{6,})/i, prefix: 'id::confirmit::', hostBound: true },
        { re: /\/s3\/(\d+\/[^\/?#]+)/i, prefix: 'id::alchemer::' },
        { re: /\/study\/([a-z0-9]{6,})/i, prefix: 'id::study::', hostBound: true, needDigit: true },
        { re: /\/survey\/([a-z0-9_-]{6,})/i, prefix: 'id::general::', hostBound: true, needDigit: true }
    ];
    const GENERIC_IDS = new Set(['overview', 'complete', 'completed', 'intro', 'start', 'thankyou', 'finished', 'status', 'results', 'entry', 'router', 'activity', 'profiler']);
    const ID_PARAMS = ['surveyid', 'survey_id', 'projectid', 'project_id', 'studyid', 'study_id', 'project', 'projid', 'vid', 'ssid', 'surveycode', 'survey_code', 'projectcode', 'project_code', 'projcode'];

    const CTRL_SEL = 'input:not([type=hidden]):not([type=submit]):not([type=button]):not([type=image]):not([type=reset]):not([type=search]):not([type=password]):not([role="combobox"]):not([role="searchbox"]), select, textarea, [role="radio"], [role="checkbox"]';
    const LABEL_SEL = 'label, [role="radio"], [role="checkbox"], option, .answer-label, .choice-text, .row-legend';
    const QUESTION_SELECTORS = ['.QuestionText', '.question-text', '.survey-question', '.q-text', '#question-title', '[data-qa="question"]', 'legend'];
    const CONTAINER_SEL = 'fieldset, [role="group"], [role="radiogroup"], [class*="question" i], [data-question], [id*="question" i]';

    /* =====================================================================
     * STORAGE
     * ===================================================================== */
    function gGet(key, def) {
        try {
            const raw = GM_getValue(key, null);
            if (raw === null || raw === undefined) return def;
            return typeof raw === 'string' ? JSON.parse(raw) : raw;
        } catch (e) { return def; }
    }
    function gSet(key, val) {
        try { GM_setValue(key, JSON.stringify(val)); } catch (e) {}
    }

    /* ---------- cross-tab mutex ---------- */
    function withLock(fn) {
        const me = Math.random().toString(36).slice(2) + Date.now().toString(36);
        const t0 = Date.now();
        while (Date.now() - t0 < 400) {
            const m = gGet(MUTEX_KEY, null);
            if (!m || Date.now() - m.ts > 1500) {
                gSet(MUTEX_KEY, { o: me, ts: Date.now() });
                const c = gGet(MUTEX_KEY, null);
                if (c && c.o === me) {
                    try { return fn(); }
                    finally {
                        const c2 = gGet(MUTEX_KEY, null);
                        if (c2 && c2.o === me) gSet(MUTEX_KEY, null);
                    }
                }
            }
        }
        return fn();
    }

    /* ---------- per-tab storage (page JS cannot read it) ---------- */
    let tabData = {};
    function tabGet(k) { return tabData[k]; }
    function tabSet(k, v) {
        if (v === undefined) delete tabData[k]; else tabData[k] = v;
        if (typeof GM_saveTab === 'function') {
            try { GM_saveTab(tabData); } catch (e) {}
        }
    }
    function loadTabData(cb) {
        if (typeof GM_getTab === 'function') {
            let done = false;
            const finish = (o) => { if (done) return; done = true; tabData = o || {}; cb(); };
            try { GM_getTab(finish); } catch (e) { finish({}); }
            setTimeout(() => finish({}), 1500);
            return;
        }
        tabData = {};
        cb();
    }
    function initTabId() {
        let id = tabGet('id');
        if (!id) {
            id = Math.random().toString(36).slice(2, 10) + Date.now().toString(36).slice(-4);
            tabSet('id', id);
        }
        return id;
    }
    function noteSeen() {
        const now = Date.now();
        let fs = tabGet('fs');
        if (!fs || fs.host !== host || now - fs.seen > IDLE_MS) {
            tabSet('fs', { host: host, ts: now, seen: now });
        } else if (now - fs.seen > 30000) {
            fs.seen = now;
            tabSet('fs', fs);
        }
    }

    /* ---------- locks ---------- */
    function lockValid(rec) {
        if (!rec || !Number.isFinite(Number(rec.ts))) return false;
        const age = Date.now() - Number(rec.ts);
        return rec.s === 'completed' && age >= 0 && age < LOCK_MS;   // only COMPLETED surveys are locked (no DQ locks / warnings)
    }
    function loadLocks() {
        // prune by the 30-day storage cap; whether a lock BLOCKS is decided later by lockValid() with the current duration
        const m = gGet(LOCKS_KEY, {});
        const out = {};
        const now = Date.now();
        for (const k of Object.keys(m || {})) {
            const r = m[k];
            if (r && r.s === 'completed' && Number.isFinite(Number(r.ts))) {
                const age = now - Number(r.ts);
                if (age >= 0 && age < MAX_LOCK_MS) out[k] = r;
            }
        }
        return out;
    }
    function mutateLocks(fn) {
        withLock(() => {
            const m = loadLocks();
            fn(m);
            gSet(LOCKS_KEY, m);
        });
    }
    function addLocks(keys, status, ts, pk, h) {
        mutateLocks(m => {
            (keys || []).forEach(k => {
                if (!k) return;
                const ex = m[k];
                if (ex && ex.s === 'completed' && status !== 'completed' && lockValid(ex)) return;
                m[k] = { s: status, ts: ts, pk: pk || '', h: h || '' };
            });
        });
    }
    function removeCompletedLocks(keys, ts) {
        mutateLocks(m => {
            (keys || []).forEach(k => { if (m[k] && m[k].s === 'completed' && m[k].ts === ts) delete m[k]; });
        });
    }

    /* ---------- completion log (spreadsheet source) ---------- */
    function loadLog() {
        const a = gGet(LOG_KEY, []);
        const now = Date.now();
        return (Array.isArray(a) ? a : []).filter(r => r && now - r.ts < LOG_KEEP_MS);
    }
    function mutateLog(fn) {
        withLock(() => {
            const a = loadLog();
            fn(a);
            gSet(LOG_KEY, a);
        });
    }

    /* ---------- active (unfinished) sessions ---------- */
    function loadActive() {
        const a = gGet(ACTIVE_KEY, []);
        const now = Date.now();
        return (Array.isArray(a) ? a : []).filter(e => e && now - e.updatedAt < ACTIVE_TTL_MS);
    }
    function mutateActive(fn) {
        return withLock(() => {
            const out = fn(loadActive());
            if (out) gSet(ACTIVE_KEY, out);
        });
    }
    function removeEntry(e) {
        if (!e) return;
        mutateActive(l => l.filter(x => x.id !== e.id));
    }
    function referrerHost() {
        try { return document.referrer ? new URL(document.referrer).hostname.toLowerCase() : ''; } catch (e) { return ''; }
    }
    function pickFinalEntry() {
        const l = loadActive();
        const mine = l.find(e => e.tabId === tabId);
        if (mine) return mine;
        const ref = referrerHost();
        const now = Date.now();
        const c = ref ? l.filter(e => now - e.updatedAt < 3 * MIN && e.host === ref) : [];
        return c.length === 1 ? c[0] : null;
    }

    /* =====================================================================
     * HELPERS
     * ===================================================================== */
    const clean = (s) => (s || '').replace(/\s+/g, ' ').trim();
    const pad2 = (n) => String(n).padStart(2, '0');

    function fmtDT(ts) {
        const d = new Date(ts);
        return d.getFullYear() + '-' + pad2(d.getMonth() + 1) + '-' + pad2(d.getDate()) + ' ' +
            pad2(d.getHours()) + ':' + pad2(d.getMinutes()) + ':' + pad2(d.getSeconds());
    }
    function fmtDate(ts) { return fmtDT(ts).slice(0, 10); }
    function dateKey(ts) { return fmtDate(ts); }
    function fmtDur(ms) {
        if (typeof ms !== 'number') return '';
        const s = Math.floor(ms / 1000);
        return Math.floor(s / 60) + 'm ' + pad2(s % 60) + 's';
    }
    function decodeSafe(s) { try { return decodeURIComponent(s); } catch (e) { return s; } }

    function hashStr(str, seed) {
        seed = seed || 0;
        let h1 = 0xdeadbeef ^ seed, h2 = 0x41c6ce57 ^ seed;
        for (let i = 0, ch; i < str.length; i++) {
            ch = str.charCodeAt(i);
            h1 = Math.imul(h1 ^ ch, 2654435761);
            h2 = Math.imul(h2 ^ ch, 1597334677);
        }
        h1 = Math.imul(h1 ^ (h1 >>> 16), 2246822507) ^ Math.imul(h2 ^ (h2 >>> 13), 3266489909);
        h2 = Math.imul(h2 ^ (h2 >>> 16), 2246822507) ^ Math.imul(h1 ^ (h1 >>> 13), 3266489909);
        return (4294967296 * (2097151 & h2) + (h1 >>> 0)).toString(36);
    }
    function normalizeForHash(s) {
        return s.normalize('NFC').toLowerCase().replace(/[^\p{L}\p{M}\p{N}\s]/gu, ' ').replace(/\s+/g, ' ').trim();
    }
    function pathExcluded() {
        const segs = location.pathname.toLowerCase().split('/').filter(Boolean);
        return segs.some(s => NON_SURVEY_SEGMENTS.has(s));
    }

    /* link key: host + path that contains an ID-like segment */
    function linkKeyFromUrl(s) {
        try {
            const u = new URL(s);
            const h = u.hostname.toLowerCase();
            if (hostInList(h, ROUTER_DOMAINS) || hostInList(h, NON_SURVEY_HOSTS) || h === 'lootwalls.com' || h.endsWith('.lootwalls.com')) return null;
            const segs = u.pathname.split('/').filter(Boolean);
            if (segs.some(x => NON_SURVEY_SEGMENTS.has(x.toLowerCase()))) return null;
            const idx = segs.findIndex(x => /^(?=.*\d)[a-z0-9_-]{8,}$/i.test(x) && !GENERIC_IDS.has(x.toLowerCase()));
            if (idx < 0) return null;
            // keep the path only up to the ID segment (drops per-user tails like /user/<uuid>)
            return 'lk::' + h + '/' + segs.slice(0, idx + 1).join('/').toLowerCase();
        } catch (e) { return null; }
    }

    /* project key from ANY url (page url or iframe src) */
    function projectKeyFromHref(href) {
        try {
            const url = new URL(href);
            const h = url.hostname.toLowerCase();
            if (hostInList(h, ROUTER_DOMAINS) || hostInList(h, NON_SURVEY_HOSTS) || h === 'lootwalls.com' || h.endsWith('.lootwalls.com')) return null;
            const segs = url.pathname.toLowerCase().split('/').filter(Boolean);
            if (segs.some(s => NON_SURVEY_SEGMENTS.has(s))) return null;
            const path = url.pathname;
            for (const p of PROJECT_PATTERNS) {
                const m = path.match(p.re);
                if (!m) continue;
                const id = m[1].toLowerCase();
                if (p.needDigit && !/\d/.test(id)) continue;
                if (GENERIC_IDS.has(id)) continue;
                return p.prefix + (p.hostBound ? h + '::' : '') + id;
            }
            if (h === 'surveymonkey.com' || h.endsWith('.surveymonkey.com')) {
                const sm = path.match(/\/r\/([^\/?#]+)/i);
                if (sm) return 'id::sm::' + sm[1].toLowerCase();
            }
            const kept = [];
            url.searchParams.forEach((val, k) => {
                const kl = k.toLowerCase();
                if (ID_PARAMS.includes(kl) && val.length >= 2 && val.length < 50) kept.push(kl + '=' + val.toLowerCase());
            });
            if (kept.length) return 'id::' + h + '::?' + kept.sort().join('&');
        } catch (e) {}
        return null;
    }
    function extractProjectKey() {
        if (pathExcluded() || isRouterDomain) return null;
        return projectKeyFromHref(location.href);
    }

    /* =====================================================================
     * STATE
     * ===================================================================== */
    let tabId = null;
    let lastHref = location.href;
    let pageEnterTime = Date.now();
    let lastRun = 0;
    let scanTimer = null;
    let lastCheapSig = '';
    let tick = 0;
    let blockActive = false;
    let lastBlock = null;
    let uiHost = null, uiRoot = null, banner = null, bannerTimer = null, overlayEl = null;
    let audioCtx = null;
    let lootHandled = '';
    let menuIds = [];
    let menuCount = -1;
    let menuAdm = null;
    let menuLic = null;
    let started = false;
    let statusLabel = '', statusKind = null, menuStatus = '';
    let gateOpen = false;              // true only while this Access ID is ACTIVE (all guard features run only then)
    let featuresStarted = false;
    let licHostEl = null;              // red screen of a BLOCKED Access ID
    let panelHost = null;              // admin Allow / Block / Pending window
    const observedRoots = new WeakSet();

    /* =====================================================================
     * CSV / SPREADSHEET
     * ===================================================================== */
    function csvCell(v) {
        let s = String(v == null ? '' : v);
        if (/^[=+\-@\t\r]/.test(s)) s = "'" + s;
        return '"' + s.replace(/"/g, '""') + '"';
    }
    function buildCsv(rows) {
        const head = ['SL', 'Survey Link', 'Start Time', 'End Time', 'Duration', 'Duration (min)', 'Speed Check (12m)', 'Status', 'Verified By', 'Locked Until', 'Domain', 'Repeat Key'];
        const out = [head.map(csvCell).join(',')];
        rows.forEach((r, i) => {
            const known = typeof r.durMs === 'number';
            const isDone = (r.status || 'Completed') === 'Completed';
            out.push([
                i + 1,
                r.link || '',
                r.start ? fmtDT(r.start) : '',
                fmtDT(r.end || r.ts),
                known ? fmtDur(r.durMs) : '',
                known ? (r.durMs / MIN).toFixed(1) : '',
                !known ? 'UNKNOWN' : (r.durMs < FAST_MS ? 'RED (<12m)' : 'OK (12m+)'),
                r.status || 'Completed',
                r.source || '',
                isDone ? fmtDT(r.ts + LOCK_MS) : '',
                r.domain || '',
                r.projectKey || r.linkKey || ''
            ].map(csvCell).join(','));
        });
        return '\uFEFF' + out.join('\r\n');
    }
    function downloadBlob(text, type, filename) {
        const blob = new Blob([text], { type: type });
        const url = URL.createObjectURL(blob);
        const a = document.createElement('a');
        a.href = url;
        a.download = filename;
        (document.body || document.documentElement).appendChild(a);
        a.click();
        a.remove();
        setTimeout(() => URL.revokeObjectURL(url), 10000);
    }
    function downloadRows(rows, filename) {
        downloadBlob(buildCsv(rows), 'text/csv;charset=utf-8;', filename);
    }
    function todaysRows() {
        const k = dateKey(Date.now());
        return loadLog().filter(r => dateKey(r.ts) === k).sort((a, b) => a.ts - b.ts);
    }

    /* =====================================================================
     * BACKUP IMPORT (merge, validated)
     * ===================================================================== */
    function importBackupText(text) {
        let d;
        try { d = JSON.parse(String(text).replace(/^\uFEFF/, '').trim()); } catch (e) { return 'Invalid JSON file.'; }
        if (!d || typeof d !== 'object') return 'Invalid backup.';
        let addedLocks = 0, addedRows = 0;

        mutateLocks(m => {
            const src = d.locks && typeof d.locks === 'object' ? d.locks : {};
            let n = 0;
            for (const k of Object.keys(src)) {
                if (++n > 5000) break;
                const v = src[k];
                if (typeof k !== 'string' || k.length > 400 || !v) continue;
                if (v.s !== 'completed' || !Number.isFinite(Number(v.ts))) continue;
                const rec = { s: v.s, ts: Number(v.ts), pk: String(v.pk || '').slice(0, 400), h: String(v.h || '').slice(0, 200) };
                if (!lockValid(rec)) continue;
                const ex = m[k];
                const better = !ex ||
                    (ex.s !== 'completed' && rec.s === 'completed') ||
                    (ex.s === rec.s && rec.ts > ex.ts);
                if (better) { m[k] = rec; addedLocks++; }
            }
        });

        mutateLog(a => {
            const ids = new Set(a.map(r => r.id));
            const src = Array.isArray(d.log) ? d.log.slice(0, 5000) : [];
            const now = Date.now();
            src.forEach(r => {
                if (!r || typeof r.id !== 'string' || ids.has(r.id)) return;
                if (!Number.isFinite(Number(r.ts)) || now - Number(r.ts) >= LOG_KEEP_MS) return;
                a.push({
                    id: r.id.slice(0, 40), ts: Number(r.ts),
                    start: Number.isFinite(Number(r.start)) ? Number(r.start) : null,
                    end: Number.isFinite(Number(r.end)) ? Number(r.end) : Number(r.ts),
                    durMs: typeof r.durMs === 'number' ? r.durMs : null,
                    link: String(r.link || '').slice(0, 1000),
                    linkKey: String(r.linkKey || '').slice(0, 400),
                    domain: String(r.domain || '').slice(0, 200),
                    projectKey: String(r.projectKey || '').slice(0, 400),
                    altKeys: Array.isArray(r.altKeys) ? r.altKeys.slice(0, 10).map(x => String(x).slice(0, 400)) : [],
                    source: String(r.source || 'Imported').slice(0, 100),
                    status: String(r.status || 'Completed').slice(0, 100)
                });
                ids.add(r.id);
                addedRows++;
            });
        });
        registerMenu(true);
        return 'Merged. New locks: ' + addedLocks + ', new sheet rows: ' + addedRows + '.';
    }
    function importBackup() {
        // A menu click is not a "real" page click, so browsers often block a hidden file picker.
        // So we show a small window with a visible file button (a real click) + a paste box as fallback.
        try {
            if (!document.documentElement) throw new Error('no root');
            const hostEl = document.createElement('div');
            hostEl.style.cssText = 'all:initial;';
            const root = hostEl.attachShadow({ mode: 'closed' });
            const close = () => { try { hostEl.remove(); } catch (e) {} };

            const wrap = mk('div', 'position:fixed;top:0;left:0;width:100%;height:100%;background:rgba(0,0,0,.75);z-index:2147483647;display:flex;align-items:center;justify-content:center;font-family:sans-serif;padding:16px;box-sizing:border-box;');
            const card = mk('div', 'background:#fff;color:#111;padding:20px;border-radius:12px;max-width:520px;width:100%;box-sizing:border-box;max-height:95vh;overflow:auto;');
            card.appendChild(mk('h3', 'margin:0 0 12px;font-size:17px;color:#111;', '📤 Import backup'));

            card.appendChild(mk('div', 'font-size:13px;margin-bottom:6px;color:#111;', 'Option 1: choose the backup .json file (imports right away)'));
            const inp = document.createElement('input');
            inp.type = 'file';
            inp.accept = '.json,application/json,text/plain';
            inp.style.cssText = 'display:block;margin:0 0 14px;font-size:13px;max-width:100%;';
            card.appendChild(inp);

            card.appendChild(mk('div', 'font-size:13px;margin-bottom:6px;color:#111;', 'Option 2: open the .json file, copy everything and paste here'));
            const ta = document.createElement('textarea');
            ta.placeholder = '{ "v": 12, "locks": { ... }, "log": [ ... ] }';
            ta.style.cssText = 'width:100%;height:90px;box-sizing:border-box;font-size:12px;margin-bottom:8px;';
            card.appendChild(ta);

            const status = mk('div', 'font-size:13px;margin:8px 0 12px;min-height:18px;word-break:break-word;font-weight:600;color:#111;', '');
            const show = (msg) => {
                status.textContent = msg;
                status.style.color = /^Merged/.test(msg) ? '#0a7a35' : '#b02a37';
            };
            card.appendChild(status);

            inp.onchange = () => {
                const f = inp.files && inp.files[0];
                if (!f) return;
                const rd = new FileReader();
                rd.onload = () => show(importBackupText(String(rd.result)));
                rd.onerror = () => show('Could not read file.');
                rd.readAsText(f);
            };

            const row = mk('div', 'display:flex;gap:10px;justify-content:flex-end;flex-wrap:wrap;');
            const pasteBtn = mk('button', 'background:#1e7e34;color:#fff;border:none;padding:10px 16px;border-radius:6px;font-weight:bold;cursor:pointer;font-size:13px;', 'Import pasted text');
            pasteBtn.onclick = () => {
                const t = ta.value.trim();
                if (!t) { show('Paste the backup text first.'); return; }
                show(importBackupText(t));
            };
            const closeBtn = mk('button', 'background:#ddd;color:#000;border:none;padding:10px 16px;border-radius:6px;font-weight:bold;cursor:pointer;font-size:13px;', 'Close');
            closeBtn.onclick = close;
            row.appendChild(pasteBtn);
            row.appendChild(closeBtn);
            card.appendChild(row);

            wrap.appendChild(card);
            root.appendChild(wrap);
            document.documentElement.appendChild(hostEl);
        } catch (e) {
            const t = prompt('Paste backup JSON:');
            if (t) alert(importBackupText(t));
        }
    }

    /* =====================================================================
     * FINALIZE
     * ===================================================================== */
    function ownKeys(entry) {
        const all = (entry.keys || []).slice();
        const pk = entry.projectKey || '';
        if (pk) return all.filter(k => !k.startsWith('id::') || k === pk);
        // no project id on the page itself (survey inside an iframe): keep only the most recent id / link key
        const lastId = all.filter(k => k.startsWith('id::')).slice(-1);
        const lastLk = all.filter(k => k.startsWith('lk::')).slice(-1);
        return all.filter(k => !k.startsWith('id::') && !k.startsWith('lk::')).concat(lastId, lastLk);
    }
    function finalizeCompleted(entry, source, lootHref) {
        const now = Date.now();
        const link = entry ? entry.link : (document.referrer || location.href);
        const row = {
            id: 'l_' + now.toString(36) + Math.random().toString(36).slice(2, 6),
            ts: now,
            start: entry ? entry.startedAt : null,
            end: now,
            durMs: entry ? Math.max(1000, now - entry.startedAt) : null,
            link: link,
            linkKey: linkKeyFromUrl(link) || '',
            domain: entry ? entry.host : host,
            projectKey: entry ? entry.projectKey : '',
            altKeys: [],
            source: source,
            status: 'Completed'
        };
        let keys = [];
        if (entry) {
            keys = ownKeys(entry);   // v13.6: lock only THIS survey's project id (never stray ids of other topics)
            if (row.linkKey && !keys.includes(row.linkKey)) keys.push(row.linkKey);
            row.altKeys = keys.filter(k => !k.startsWith('qo::') && !k.startsWith('qq::')).slice(0, 10);
        }
        mutateLog(a => { a.push(row); });
        if (entry) {
            addLocks(keys, 'completed', now, entry.projectKey, entry.host);
            removeEntry(entry);
        }
        gSet(LASTFINAL_KEY, { ts: now, id: row.id, lootHref: lootHref || '', keys: keys });
        tabSet('lastq', undefined); tabSet('utgone', undefined);   // v14.4: UserTesting end-detection state is finished
        tabSet('ov', undefined);
        tabSet('done', {
            href: location.href,
            projectKey: entry ? entry.projectKey : '',
            linkKey: row.linkKey || linkKeyFromUrl(location.href) || '',
            ts: now
        });
        return row;
    }

    /* =====================================================================
     * LOOTWALLS (silent, nothing added to page)
     * ===================================================================== */
    const isLootStatusUrl = (u) => u.includes('lootwalls.com/cint/status');
    const isLootCompletedUrl = (u) => isLootStatusUrl(u) && u.includes('status=completed');

    function navType() {
        try {
            const n = performance.getEntriesByType('navigation')[0];
            return n ? n.type : '';
        } catch (e) { return ''; }
    }

    function recordLootwallsCompletion() {
        const href = location.href;
        const now = Date.now();
        const lf = gGet(LASTFINAL_KEY, null);
        const entry = pickFinalEntry();
        const newerEntry = !!(lf && entry && entry.startedAt > lf.ts);
        const nt = navType();

        if (lf && lf.lootHref === href && (nt === 'reload' || nt === 'back_forward' || (entry && entry.updatedAt <= lf.ts))) {
            return { kind: 'already' };
        }

        if (lf && !lf.lootHref && now - lf.ts < 5 * MIN && !newerEntry) {
            let verifiedRow = null;
            mutateLog(a => {
                const row = a.find(r => r.id === lf.id);
                if (row) { row.source = 'Survey end + Lootwalls verified'; verifiedRow = row; }
            });
            if (verifiedRow) {
                lf.lootHref = href;
                gSet(LASTFINAL_KEY, lf);
                tabSet('done', {
                    href: href,
                    projectKey: verifiedRow.projectKey || '',
                    linkKey: verifiedRow.linkKey || '',
                    ts: now
                });
                return { kind: 'verified', row: verifiedRow };
            }
        }

        if (entry) return { kind: 'saved', row: finalizeCompleted(entry, 'Lootwalls status=completed', href) };
        return { kind: 'unknown', row: finalizeCompleted(null, 'Lootwalls (no timer data)', href) };
    }

    function handleLootwallsEnded(u) {
        const now = Date.now();
        const entry = pickFinalEntry();
        const lf = gGet(LASTFINAL_KEY, null);

        if (lf && !lf.lootHref && !lf.undone && now - lf.ts < 5 * MIN && !(entry && entry.startedAt > lf.ts)) {
            removeCompletedLocks(lf.keys, lf.ts);
            mutateLog(a => {
                const row = a.find(r => r.id === lf.id);
                if (row) { row.status = 'Disqualified (Lootwalls: not completed)'; row.source = 'Corrected by Lootwalls'; }
            });
            lf.undone = true;
            gSet(LASTFINAL_KEY, lf);
        }

        if (!entry) return;
        removeEntry(entry);
    }

    function lootwallsTick() {
        if (!gateOpen) return;
        const href = location.href;
        const u = decodeSafe(href).toLowerCase();
        if (!isLootStatusUrl(u) || lootHandled === href) return;
        lootHandled = href;
        if (isLootCompletedUrl(u)) {
            const res = recordLootwallsCompletion();
            dbg('lootwalls result', res);
        } else {
            handleLootwallsEnded(u);
        }
        registerMenu(true);
    }

    /* =====================================================================
     * VISIBILITY / DOM SCAN
     * ===================================================================== */
    function isVisible(el) {
        try {
            const view = el.ownerDocument.defaultView || window;
            let node = el, depth = 0;
            while (node && node.nodeType === 1 && depth++ < 16) {
                if (node.hidden || node.hasAttribute('inert') || node.getAttribute('aria-hidden') === 'true') return false;
                const cs = view.getComputedStyle(node);
                if (cs.display === 'none' || cs.visibility === 'hidden' || Number(cs.opacity) === 0) return false;
                node = node.parentElement;
            }
            const r = el.getBoundingClientRect();
            return r.width > 0 || r.height > 0;
        } catch (e) { return false; }
    }
    function isActiveControl(el) {
        if (el.disabled) return false;
        try { if (el.closest && el.closest('[role="search"], [role="searchbox"]')) return false; } catch (e) {}
        if (isVisible(el)) return true;
        try {
            if (el.labels && el.labels.length && Array.from(el.labels).some(isVisible)) return true;
            const lab = el.closest && el.closest('label');
            if (lab && isVisible(lab)) return true;
        } catch (e) {}
        return false;
    }
    function collectRoots() {
        const roots = [document];
        const seen = new Set(roots);
        for (let i = 0; i < roots.length && roots.length < 30; i++) {
            let all;
            try { all = roots[i].querySelectorAll('*'); } catch (e) { continue; }
            const cap = Math.min(all.length, 4000);
            for (let j = 0; j < cap; j++) {
                const n = all[j];
                let sub = null;
                if (n.shadowRoot) sub = n.shadowRoot;
                else if (n.tagName === 'IFRAME' || n.tagName === 'FRAME') {
                    try { const d = n.contentDocument; if (d && d.documentElement) sub = d; } catch (e) {}
                }
                if (sub && !seen.has(sub)) { seen.add(sub); roots.push(sub); }
            }
        }
        return roots;
    }
    function visibleControls(roots) {
        const out = [];
        for (const r of roots) {
            let els;
            try { els = r.querySelectorAll(CTRL_SEL); } catch (e) { continue; }
            for (const el of els) {
                if (isActiveControl(el)) { out.push(el); if (out.length >= 80) return out; }
            }
        }
        return out;
    }

    /* cross-origin survey iframes: we cannot read inside, but we can read their src */
    function iframeKeys() {
        const out = new Set();
        try {
            document.querySelectorAll('iframe[src]').forEach(f => {
                const src = f.src;
                if (!src || !/^https?:/i.test(src)) return;
                const r = f.getBoundingClientRect();
                if (r.width < IFRAME_MIN_W || r.height < IFRAME_MIN_H) return;   // ignore ads / trackers
                const lk = linkKeyFromUrl(src);
                const pk = projectKeyFromHref(src);
                if (lk) out.add(lk);
                if (pk) out.add(pk);
            });
        } catch (e) {}
        return Array.from(out).slice(0, 6);
    }

    function isGenericQuestion(q) {
        return /\b(?:your age|how old|age group|age range|year of birth|date of birth|birth ?day|gender|are you (?:a )?(?:male|female)|sex|zip|postal|post ?code|marital|household income|annual income|income|ethnic\w*|race|education|employ\w*|occupation|number of (?:people|adults|children)|household|children|country|state (?:do you|of) (?:live|reside)|i agree|consent|terms (?:and|&) conditions|privacy|attention check|captcha|are you human)\b/i.test(q) ||
               /বয়স|লিঙ্গ|জেন্ডার|পোস্টাল|আয়|শিক্ষা|পেশা|বৈবাহিক/.test(q);
    }
    function normalizeQuestion(q) {
        return clean(q)
            .replace(/^(?:q(?:uestion)?\s*\d+|\d+)[\.\)\:\-\s]+/i, '')
            .replace(/\b\d+\s*(?:\/|of|out of)\s*\d+\b/gi, '')
            .trim();
    }
    function explicitQuestionElements(roots) {
        const out = [];
        const seen = new Set();
        for (const r of roots) {
            for (const sel of QUESTION_SELECTORS) {
                let els;
                try { els = r.querySelectorAll(sel); } catch (e) { continue; }
                for (const el of els) {
                    if (!el || seen.has(el) || !isVisible(el)) continue;
                    seen.add(el);
                    const len = (el.textContent || '').length;
                    if (len >= 15 && len <= 800) out.push(el);
                    if (out.length >= MAX_QUESTION_CANDIDATES) return out;
                }
            }
        }
        return out;
    }
    function questionNearControl(ctrl) {
        let el = ctrl.parentElement, fallback = '';
        for (let i = 0; i < 8 && el; i++, el = el.parentElement) {
            if (el === el.ownerDocument.body || el === el.ownerDocument.documentElement) break;
            if ((el.textContent || '').length > 1200) break;
            const text = (el.innerText || '').trim();
            if (text.length < 20 || text.length > 900) continue;
            const lines = text.split(/\n+/).map(clean).filter(l => l.length >= 12 && l.length <= 500);
            const withQ = lines.find(l => /[?？؟]/.test(l));
            if (withQ) return withQ;
            if (!fallback) fallback = lines.find(l => l.length >= 25) || '';
        }
        return fallback;
    }
    function questionContainerFor(el) {
        const parent = el.parentElement;
        if (!parent) return el;
        try {
            const c = parent.closest(CONTAINER_SEL);
            if (c && (c.textContent || '').length <= 1400) return c;
        } catch (e) {}
        let node = parent;
        for (let i = 0; i < 4 && node; i++, node = node.parentElement) {
            if ((node.textContent || '').length > 1400) break;
            let n = 0;
            try { n = node.querySelectorAll(CTRL_SEL).length; } catch (e) {}
            if (n > 0 && n <= 12) return node;
        }
        return parent;
    }
    function collectLabels(container) {
        const set = new Set();
        if (!container || !container.querySelectorAll) return [];
        let els;
        try { els = container.querySelectorAll(LABEL_SEL); } catch (e) { return []; }
        for (const el of els) {
            const t = clean((el.getAttribute && el.getAttribute('aria-label')) || el.textContent);
            if (t.length >= 2 && t.length <= 100) set.add(normalizeForHash(t));
            if (set.size >= 16) break;
        }
        return Array.from(set).sort();
    }
    /* fp  = question + sorted option labels (strict)
       fp2 = question text only (fuzzy: survives option shuffle / option text change) */
    function makeQuestionFingerprint(q, container) {
        q = normalizeQuestion(q);
        if (q.length < 15 || q.length > 600) return null;
        if (q.length < 120 && isGenericQuestion(q)) return null;
        const qNorm = normalizeForHash(q);
        if (qNorm.length < 15) return null;
        const labels = collectLabels(container);
        const combo = normalizeForHash(qNorm + ' :: ' + labels.join(' | '));
        if (combo.length < 25) return null;
        // v14.4: on UserTesting a question of 25+ characters also gets the fuzzy key (short questions are common there)
        const fp2 = (qNorm.length >= 40 || (IS_UT && qNorm.length >= 25)) ? 'qq::' + hashStr(qNorm, 7) : '';   // short generic text is too risky for fuzzy
        return { fp: 'qo::' + hashStr(combo), fp2: fp2, question: q };
    }
    function scanQuestions(roots, ctrls) {
        if (pathExcluded() || !ctrls.length || isRouterDomain) return [];
        const out = [];
        const seenFp = new Set();
        const addItem = (item) => {
            if (!item || seenFp.has(item.fp)) return;
            seenFp.add(item.fp);
            out.push(item);
        };
        for (const el of explicitQuestionElements(roots)) {
            addItem(makeQuestionFingerprint(clean(el.innerText || el.textContent), questionContainerFor(el)));
            if (out.length >= MAX_FINGERPRINTS_PER_PAGE) break;
        }
        if (out.length < MAX_FINGERPRINTS_PER_PAGE) {
            const doneParents = new Set();
            let used = 0;
            for (const ctrl of ctrls) {
                if (used >= MAX_FALLBACK_CONTROLS || out.length >= MAX_FINGERPRINTS_PER_PAGE) break;
                const par = ctrl.parentElement;
                if (par && doneParents.has(par)) continue;
                if (par) doneParents.add(par);
                used++;
                const q = questionNearControl(ctrl);
                if (!q) continue;
                addItem(makeQuestionFingerprint(q, questionContainerFor(ctrl)));
            }
        }
        return out;
    }

    /* ---------- terminal (end page) detection ---------- */
    const DQ_URL = /(?:[?&\/_\-=])(screenout|screen_out|screen-out|disqualif\w*|quotafull|quota_full|overquota|terminate)(?:[&\/_\-=.]|$)/i;
    const OK_URL = /(?:[?&\/_\-=])(status=completed|status=complete|survey_complete|surveycomplete|end=complete|completed=true|result=complete|complete=1|is_complete=true)(?:[&\/_\-=]|$)/i;
    const DQ_TEXT = /(?:you (?:did not|didn't|do not|don't) qualify|you (?:are|were) not eligible|you have been disqualified|did not qualify for this survey|screened out|quota (?:is )?full|quota has been met|survey is (?:now )?closed|no longer accepting)/i;
    const OK_PHRASES = [
        'thank you for completing', 'thanks for completing', 'your response has been recorded',
        'your responses have been recorded', 'successfully completed the survey',
        'you have completed the survey', 'survey is complete', 'survey completed',
        'you have successfully completed', 'survey has been completed',
        'your answers have been saved'
    ];
    function detectTerminal(ctrls) {
        if (ctrls.length || !document.body) return null;
        if (Date.now() - pageEnterTime < 2000) return null;
        const u = location.href.toLowerCase();
        if (DQ_URL.test(u)) return 'dq';
        if (OK_URL.test(u)) return 'completed';
        const t = clean(document.body.innerText || '').toLowerCase();
        if (t.length < 10 || t.length > MAX_SIGNAL_TEXT) return null;
        if (DQ_TEXT.test(t)) return 'dq';
        if (OK_PHRASES.some(p => t.includes(p))) return 'completed';
        return null;
    }

    /* =====================================================================
     * ACTIVE SESSION
     * ===================================================================== */
    function addKey(e, k, sig) {
        if (!k || e.keys.includes(k)) return false;
        e.keys.push(k);
        if (sig) e.pageOf[k] = sig;
        if (e.keys.length > MAX_KEYS) {
            const drop = e.keys.shift();
            delete e.pageOf[drop];
            if (e.qq) delete e.qq[drop];
        }
        return true;
    }
    function qCountOf(e) { return e.keys.filter(k => k.startsWith('qo::')).length; }

    function touchEntry(projKey, linkKey, fps, ik) {
        let result = null;
        mutateActive(list => {
            const now = Date.now();
            let e = list.find(x => x.tabId === tabId);

            if (e && (now - e.updatedAt > IDLE_MS ||
                (projKey && e.projectKey && e.host === host && e.projectKey !== projKey) ||
                (e.host !== host && now - e.updatedAt > HOST_GAP_MS))) {
                list = list.filter(x => x.id !== e.id);
                e = null;
                tabSet('ov', undefined);
            }

            let changed = false;
            if (!e) {
                const ref = referrerHost();
                const cands = ref ? list
                    .filter(x => x.tabId !== tabId && x.host !== host && x.host === ref && now - x.updatedAt < ADOPT_MS)
                    .sort((a, b) => b.updatedAt - a.updatedAt) : [];
                if (cands[0]) {
                    e = cands[0];
                    e.tabId = tabId;
                } else {
                    const fs = tabGet('fs');
                    const startedAt = (fs && fs.host === host && now - fs.seen < IDLE_MS && fs.ts <= now) ? fs.ts : now;
                    e = {
                        id: 's_' + now.toString(36) + Math.random().toString(36).slice(2, 6),
                        tabId: tabId, host: host, link: location.href,
                        startedAt: startedAt, updatedAt: now,
                        projectKey: '', keys: [], pageOf: {}, qq: {}, fresh: false
                    };
                    list.push(e);
                }
                changed = true;
            }
            if (!e.qq) e.qq = {};

            if (e.host !== host) { e.host = host; changed = true; }
            if (projKey) {
                e.projectKey = projKey;
                if (addKey(e, projKey, '')) changed = true;
            }
            if (linkKey && addKey(e, linkKey, '')) changed = true;
            (ik || []).forEach(k => { if (addKey(e, k, '')) changed = true; });
            const sig = fps.length ? fps[0].fp : '';
            fps.forEach(it => {
                if (addKey(e, it.fp, sig)) changed = true;
                if (it.fp2) {
                    if (addKey(e, it.fp2, '')) changed = true;
                    if (e.qq[it.fp] !== it.fp2) { e.qq[it.fp] = it.fp2; changed = true; }
                }
            });

            result = e;
            if (changed || now - e.updatedAt > 15000) {
                e.updatedAt = now;
                return list;
            }
            return null;
        });
        return result;
    }
    function saveEntryFlags(entry) {
        mutateActive(list => {
            const i = list.findIndex(x => x.id === entry.id);
            if (i < 0) return null;
            list[i] = entry;
            return list;
        });
    }
    function heartbeat() {
        mutateActive(l => {
            const e = l.find(x => x.tabId === tabId);
            if (e && Date.now() - e.updatedAt > 25000) { e.updatedAt = Date.now(); return l; }
            return null;
        });
    }

    /* =====================================================================
     * UI (banner + block overlay only)
     * ===================================================================== */
    function mk(tag, css, text) {
        const e = document.createElement(tag);
        if (css) e.style.cssText = css;
        if (text !== undefined && text !== null) e.textContent = text;
        return e;
    }
    function ui() {
        const parent = document.documentElement;
        if (!parent) return null;
        if (!uiHost || !uiHost.isConnected) {
            uiHost = document.createElement('div');
            uiHost.style.cssText = 'all:initial;';
            uiRoot = uiHost.attachShadow({ mode: 'closed' });
            parent.appendChild(uiHost);
            overlayEl = null; banner = null;
        }
        return uiRoot;
    }
    function notify(title, msg) {
        try {
            if (typeof GM_notification === 'function') {
                GM_notification({ title: title, text: msg, timeout: 8000, silent: true });
            }
        } catch (e) {}
    }
    function freshSignal(entry) {
        const msg = 'No duplicate found. Timer started ' + fmtDT(entry.startedAt) + '. Take at least 12 minutes.';
        notify('✅ Fresh survey', msg);
        try { if (navigator.vibrate) navigator.vibrate(120); } catch (e) {}
        if (!GREEN_BADGE || blockActive) return;
        const root = ui();
        if (!root) return;
        const el = mk('div', 'position:fixed;top:max(10px,env(safe-area-inset-top,0px));right:10px;z-index:2147483647;background:#1e9e4a;color:#fff;padding:6px 12px;border-radius:999px;font:600 12px sans-serif;box-shadow:0 2px 8px rgba(0,0,0,.35);pointer-events:none;', '✅ New survey');
        root.appendChild(el);
        setTimeout(() => {
            try { el.remove(); } catch (e) {}
            // leave no trace: remove our host element too (unless the block screen is using it)
            if (!blockActive && uiHost) {
                try { uiHost.remove(); } catch (e) {}
                uiHost = null; uiRoot = null; overlayEl = null; banner = null;
            }
        }, GREEN_BADGE_MS);
    }
    function showBanner(title, msg, color) {
        if (blockActive) return;
        if (QUIET_MODE) { notify(title, msg); return; }
        const root = ui();
        if (!root) return;
        if (banner && banner.isConnected) banner.remove();
        banner = mk('div', 'position:fixed;top:max(15px,env(safe-area-inset-top,0px));right:15px;z-index:2147483647;background:' + color + ';color:#fff;padding:12px 16px;border-radius:8px;font-family:sans-serif;box-shadow:0 4px 15px rgba(0,0,0,0.4);max-width:350px;font-size:13px;line-height:1.4;');
        banner.appendChild(mk('div', 'font-weight:bold;margin-bottom:4px;', title));
        banner.appendChild(mk('div', '', msg));
        root.appendChild(banner);
        clearTimeout(bannerTimer);
        bannerTimer = setTimeout(() => { if (banner) banner.remove(); }, 8000);
    }
    function playBeep() {
        try {
            audioCtx = audioCtx || new (window.AudioContext || window.webkitAudioContext)();
            if (audioCtx.state === 'suspended') audioCtx.resume().catch(() => {});
            const osc = audioCtx.createOscillator();
            const gain = audioCtx.createGain();
            osc.type = 'triangle';
            osc.frequency.setValueAtTime(750, audioCtx.currentTime);
            gain.gain.setValueAtTime(0.2, audioCtx.currentTime);
            osc.connect(gain); gain.connect(audioCtx.destination);
            osc.start(); osc.stop(audioCtx.currentTime + 0.3);
        } catch (e) {}
        try { if (navigator.vibrate) navigator.vibrate([200, 100, 200]); } catch (e) {}
    }
    function clearBlock() {
        blockActive = false;
        lastBlock = null;
        setStatus(null);
        if (overlayEl) { try { overlayEl.remove(); } catch (e) {} }
        overlayEl = null;
    }
    function renderOverlay() {
        const root = ui();
        if (!root || !lastBlock) return;
        if (overlayEl && overlayEl.isConnected) return;
        const rec = lastBlock.rec;
        overlayEl = mk('div', 'position:fixed;top:0;left:0;width:100%;height:100%;background:rgba(120,10,20,0.97);z-index:2147483647;display:flex;align-items:center;justify-content:center;font-family:sans-serif;color:#fff;text-align:center;padding:20px;box-sizing:border-box;');
        const card = mk('div', 'background:rgba(0,0,0,0.5);padding:28px;border-radius:12px;max-width:560px;width:100%;border:2px solid #ff4d4d;');
        card.appendChild(mk('h2', 'margin:0 0 10px;color:#ffeb3b;font-size:20px;line-height:1.3;', '⛔ You already completed this survey'));
        card.appendChild(mk('p', 'font-size:15px;line-height:1.5;margin:0 0 10px;', 'Same survey detected. It is blocked for ' + LOCK_DAYS + ' days after completion.'));
        if (rec) {
            card.appendChild(mk('div', 'font-size:12px;opacity:.9;margin:10px 0;word-break:break-word;',
                'Completed: ' + fmtDT(rec.ts) + '  |  Allowed again after: ' + fmtDT(rec.ts + LOCK_MS)));
        }
        card.appendChild(mk('div', 'font:11px monospace;opacity:.7;margin:6px 0;word-break:break-all;',
            'Survey: ' + (lastBlock.pk || '-') + '  |  ' + (getEmpName() ? getEmpName() + '  |  ' : '') + 'ID: ' + getClientId()));
        const row = mk('div', 'display:flex;gap:10px;justify-content:center;flex-wrap:wrap;margin-top:12px;');
        const closeBtn = mk('button', 'background:#ffeb3b;color:#000;border:none;padding:12px 20px;border-radius:6px;font-weight:bold;cursor:pointer;font-size:14px;', 'Close tab');
        closeBtn.onclick = () => { try { window.close(); } catch (e) {} };
        row.appendChild(closeBtn);
        card.appendChild(row);
        overlayEl.appendChild(card);
        root.appendChild(overlayEl);
    }
    function enforceBlock(rec, pk) {
        if (blockActive) return;
        blockActive = true;
        setStatus('repeat', null, rec);
        lastBlock = { rec: rec, pk: pk || '', href: location.href };
        if (banner && banner.isConnected) banner.remove();
        notify('⛔ Duplicate survey blocked', 'You already completed this survey. Locked until ' + fmtDT(rec.ts + LOCK_MS));
        playBeep();
        renderOverlay();
    }
    function overrideActive(projKey) {
        const ov = tabGet('ov');
        if (!ov || typeof ov !== 'object') return false;
        if (ov.pk && projKey) return ov.pk === projKey;
        return ov.host === host && Date.now() - ov.ts < IDLE_MS;
    }

    /* =====================================================================
     * EVALUATION
     * ===================================================================== */
    function evaluate(entry, projKey, linkKey, locks, log, extraKeys) {
        const out = { block: null, matches: 0 };
        const now = Date.now();
        const direct = [projKey, linkKey].concat(extraKeys || []).filter(Boolean);

        // v13.6 FIX: a lock that belongs to ANOTHER project id (r.pk) must not block this project
        const myIds = [projKey, linkKey].filter(Boolean);
        const ulist = myIds.length ? adminUnlockList().filter(u => myIds.includes(u.pk) && (!u.id || u.id === getClientId())) : [];
        const remoteUnlocked = (ts) => ulist.some(u => Number(ts) <= u.ts);   // v14.1: admin unlock (published list)
        const foreign = (k, pk0) => !!(projKey && pk0 && k.startsWith('id::') && pk0 !== projKey);
        // v13.7: LEGACY locks (made by old versions, no owner project). One completion locked EVERY id it had seen,
        // so one session can hold several ids and only one of them is real.
        //  - the log row of that completion remembers the first link -> its project id is the REAL one
        //  - no usable link and 2+ ids at the same time -> ambiguous -> do not block on the id alone
        const legacyForeign = (k, r) => {
            if (!projKey || !r || r.pk || !k.startsWith('id::')) return false;
            const row = log.find(x => x && x.ts === r.ts && x.link);
            const truth = row ? (projectKeyFromHref(row.link) || '') : '';
            if (truth) return truth !== k;
            const same = Object.keys(locks).filter(x => x.startsWith('id::') && locks[x] && locks[x].ts === r.ts && !locks[x].pk);
            return same.length >= 2;
        };
        direct.forEach(k => {
            const r = locks[k];
            if (r && lockValid(r)) {
                if (remoteUnlocked(r.ts)) return;
                if (foreign(k, r.pk) || legacyForeign(k, r)) return;
                if (!out.block) out.block = r;
                out.matches++;
            }
        });

        // safety net: the completed-survey log itself (works even if a lock was lost)
        if (!out.block && direct.length) {
            const hit = log.find(r => {
                if (!r || r.unlocked || (r.status || 'Completed') !== 'Completed' || now - r.ts >= LOCK_MS || remoteUnlocked(r.ts)) return false;
                const rl = r.linkKey || linkKeyFromUrl(r.link || '');
                const pool = [r.projectKey, rl].concat(r.altKeys || []).filter(Boolean);
                const rowTruth = (projKey && !r.projectKey) ? (projectKeyFromHref(r.link || '') || '') : '';
                return direct.some(k => pool.includes(k) && !foreign(k, r.projectKey) && !(rowTruth && k.startsWith('id::') && rowTruth !== k));
            });
            if (hit) { out.block = { s: 'completed', ts: hit.ts }; out.matches++; }
        }

        if (entry) {
            // non-question keys collected earlier in this session (iframe keys, earlier project keys)
            entry.keys.forEach(k => {
                if (k.startsWith('qo::') || k.startsWith('qq::')) return;
                const r = locks[k];
                if (r && lockValid(r)) {
                    if (remoteUnlocked(r.ts)) return;
                    if (foreign(k, r.pk) || legacyForeign(k, r)) return;
                    if (!out.block) out.block = r;
                    out.matches++;
                }
            });

            // question matches: strict key OR its fuzzy (question-only) partner
            const comp = [];
            const qmap = entry.qq || {};
            const myPk = entry.projectKey || projKey || '';
            entry.keys.forEach(k => {
                if (!k.startsWith('qo::')) return;
                let r = locks[k], fuzzy = false;
                if (!lockValid(r)) { const k2 = qmap[k]; r = k2 ? locks[k2] : null; fuzzy = true; }
                if (!lockValid(r) || remoteUnlocked(r.ts)) return;
                let weak = false;
                if (myPk) {
                    if (r.pk && r.pk !== myPk) return;     // locked by a DIFFERENT project (same client, other topic) -> not a repeat
                    if (!r.pk && fuzzy) return;             // old lock without project info: question-only match is too weak
                    if (!r.pk) weak = true;                 // v13.6: old lock without project info -> needs a MUCH stronger match
                } else if (r.h && r.h !== entry.host) return;   // no project ID: only locks from the same site can match
                comp.push({ k: k, r: r, weak: weak });
            });
            const strong = comp.filter(c => !c.weak), weakL = comp.filter(c => c.weak);
            const pgs = (arr) => new Set(arr.map(c => entry.pageOf[c.k]).filter(Boolean));
            // v14.4: UserTesting shows ONE question per page, so 2 matching questions on 2 pages are enough there
            const minM = IS_UT ? 2 : MIN_MATCHES;
            const okStrong = strong.length >= SINGLE_PAGE_MATCHES || (strong.length >= minM && pgs(strong).size >= MIN_MATCH_PAGES);
            const okWeak = weakL.length >= 8 && pgs(weakL).size >= 3;
            if (!out.block && (okStrong || okWeak)) out.block = (okStrong ? strong : weakL)[0].r;
            out.matches += comp.length;
        }
        return out;
    }

    /* EARLY check by URL only: runs at document-start and again every ~10s */
    /* v14.1: a page that shows no question yet (captcha / intro) is never blocked; the block starts at the first real question page (runScan). */
    function urlPrecheck() { /* intentionally empty */ }

    /* =====================================================================
     * MAIN SCAN
     * ===================================================================== */
    /* v14.4 UserTesting: true while a "N of N" (last question) page was seen in this tab within the last 60 min */
    function utPending() {
        const lq = tabGet('lastq');
        return !!(lq && Date.now() - lq.ts < 60 * MIN);
    }

    function runScan() {
        if (!gateOpen) return;
        if (adminBlocked) return;
        lastRun = Date.now();
        if (!document.body) return;

        if (blockActive) {
            if (lastBlock && lastBlock.href !== location.href) clearBlock();
            else return;
        }

        const href = location.href;
        if (href !== lastHref) { lastHref = href; pageEnterTime = Date.now(); }
        if (pathExcluded()) return;

        noteSeen();
        const projKey = extractProjectKey();
        const linkKey = isRouterDomain ? null : linkKeyFromUrl(href);

        const dn = tabGet('done');
        if (dn && Date.now() - dn.ts < DONE_MS && (dn.href === href || (projKey && dn.projectKey === projKey) || (linkKey && dn.linkKey === linkKey))) { setStatus(null); return; }

        const roots = collectRoots();
        observeRoots(roots);
        const ctrls = visibleControls(roots);
        const fps = scanQuestions(roots, ctrls);
        const ik = isRouterDomain ? [] : iframeKeys();
        const now = Date.now();

        const mine = loadActive().find(e => e.tabId === tabId) || null;

        // v14.4 UserTesting: remember the LAST question page ("9 of 9"). When that progress bar is gone for 3 s
        // (and the question is gone too), the study is finished. Works even if the end page has inputs or no known text.
        let utDone = false;
        if (IS_UT && mine && qCountOf(mine) >= MIN_QUESTIONS_FOR_FINAL) {
            let isLast = false, still = false;
            try {
                const txt = (document.body.innerText || '').slice(0, 5000);
                const re = /\b(\d{1,3})\s*(?:of|\/)\s*(\d{1,3})\b/gi;
                let pm;
                while ((pm = re.exec(txt))) {
                    still = true;                                                    // some "N of N" progress text is on the page
                    if (pm[1] === pm[2] && Number(pm[2]) >= 3) { isLast = true; break; }   // "9 of 9" = last question
                }
            } catch (e) {}
            if (isLast) {
                tabSet('lastq', { id: mine.id, ts: now, fp: fps.length ? fps[0].fp : '' });
                tabSet('utgone', undefined);
            } else {
                const lq = tabGet('lastq');
                if (lq && lq.id === mine.id && now - lq.ts < 60 * MIN) {
                    const sameQ = !!(fps.length && lq.fp && fps[0].fp === lq.fp);
                    if (still || sameQ) tabSet('utgone', undefined);
                    else {
                        const g = tabGet('utgone');
                        if (!g || g.id !== mine.id) tabSet('utgone', { id: mine.id, ts: now });
                        else if (now - g.ts > 3000) utDone = true;
                    }
                }
            }
        }

        // survey's own end page
        if (mine && (utDone || (!fps.length && qCountOf(mine) >= MIN_QUESTIONS_FOR_FINAL && now - mine.startedAt > 45000))) {
            const term = utDone ? 'completed' : detectTerminal(ctrls);
            if (term === 'completed') {
                const row = finalizeCompleted(mine, utDone ? 'Survey end (UserTesting)' : 'Survey end page');
                setStatus(null);   // survey finished: status button disappears
                registerMenu(true);
                const fast = typeof row.durMs === 'number' && row.durMs < FAST_MS;
                if (fast) {
                    showBanner('🔴 Completed TOO FAST (' + fmtDur(row.durMs) + ')',
                        'Under 12 minutes: reversal risk. Locked for ' + LOCK_DAYS + ' days (until ' + fmtDate(now + LOCK_MS) + ').', '#b02a37');
                } else {
                    showBanner('✅ Completed & locked', (typeof row.durMs === 'number' ? 'Time ' + fmtDur(row.durMs) + '. ' : '') +
                        'Locked for ' + LOCK_DAYS + ' days (until ' + fmtDate(now + LOCK_MS) + ').', '#1e7e34');
                }
                return;
            }
            if (term === 'dq') {
                removeEntry(mine);      // screen-out: nothing is locked, nothing is shown
                setStatus(null);
                return;
            }
        }

        if (!projKey && !fps.length && !ik.length) { if (!mine) setStatus(null); return; }

        const entry = touchEntry(projKey, linkKey, fps, ik) || mine;

        const locks = loadLocks();
        const log = loadLog();
        const verdict = evaluate(entry, projKey, linkKey, locks, log, ik);

        if (verdict.block && !overrideActive(projKey)) {
            const hasQuestion = fps.length > 0 || (entry && qCountOf(entry) > 0);
            if (hasQuestion) {
                enforceBlock(verdict.block, projKey);
                return;
            }
            setStatus('checking', entry);   // captcha / intro page: no topic visible yet -> wait for the first question
            return;
        }

        if (verdict.block) setStatus('repeat', entry, verdict.block);      // only reached if you chose "continue anyway"
        else if (entry && qCountOf(entry) >= MIN_QUESTIONS_FOR_FINAL) setStatus('fresh', entry);
        else setStatus('checking', entry);

        if (entry && !entry.fresh && !verdict.matches && !verdict.block &&
            qCountOf(entry) >= MIN_QUESTIONS_FOR_FINAL && now - pageEnterTime >= INITIAL_PAGE_GRACE_MS) {
            entry.fresh = true;
            saveEntryFlags(entry);
            freshSignal(entry);
        }
    }

    function scheduleScan(delay) {
        if (scanTimer) return;
        const wait = Math.max(delay || SCAN_DEBOUNCE_MS, MIN_SCAN_INTERVAL_MS - (Date.now() - lastRun), 0);
        scanTimer = setTimeout(() => {
            // run when the browser is idle so the survey page never lags or freezes
            const run = () => { scanTimer = null; try { runScan(); } catch (e) { dbg('scan error', e); } };
            scanTimer = 1;
            if (typeof window.requestIdleCallback === 'function') window.requestIdleCallback(run, { timeout: 2500 });
            else setTimeout(run, 0);
        }, wait);
    }
    function cheapSignature() {
        if (!document.body) return '';
        return location.href + '|' + document.title + '|' + document.body.childElementCount + '|' +
            document.querySelectorAll('input,select,textarea,[role="radio"],[role="checkbox"]').length + '|' +
            document.querySelectorAll('iframe').length;
    }
    function pollTick() {
        if (!gateOpen) return;
        if (adminBlocked) return;
        if (document.hidden) return;
        tick++;
        if (blockActive && lastBlock) {
            if (location.href !== lastBlock.href) { clearBlock(); scheduleScan(200); return; }
            if (!uiHost || !uiHost.isConnected) renderOverlay();
        }
        if (location.href !== lastHref) { scheduleScan(200); return; }
        const sig = cheapSignature();
        if (sig !== lastCheapSig) { lastCheapSig = sig; scheduleScan(); }
        // v14.4: a static end page does not change the DOM, so keep re-checking while the "N of N" state is waiting
        if (IS_UT && tick % 2 === 0 && utPending()) scheduleScan();
        if (tick % 4 === 0 && !blockActive) { try { urlPrecheck(); } catch (e) {} }   // catches a lock added by another tab
        if (tick % 24 === 0 && (statusKind === 'fresh' || statusKind === 'checking')) {
            const e = loadActive().find(x => x.tabId === tabId);
            if (e) setStatus(statusKind, e);          // refresh the minute counter
        }
        if (tick % 12 === 0) { heartbeat(); syncLockDays(); registerMenu(false); }
    }
    function isOwnMutation(m) {
        const nodes = Array.prototype.slice.call(m.addedNodes).concat(Array.prototype.slice.call(m.removedNodes));
        return nodes.length > 0 && nodes.every(n => n === uiHost || n === adminHostEl || n === licHostEl);
    }
    function observeRoots(roots) {
        for (const root of roots) {
            if (observedRoots.has(root)) continue;
            try {
                const mo = new MutationObserver(muts => {
                    if (muts.every(isOwnMutation)) return;
                    scheduleScan();
                });
                mo.observe(root, {
                    childList: true, subtree: true, characterData: true, attributes: true,
                    attributeFilter: ['hidden', 'aria-hidden', 'class', 'disabled', 'role', 'aria-label', 'data-question', 'src']
                });
                observedRoots.add(root);
            } catch (e) {}
        }
    }

    /* =====================================================================
     * MENU (Tampermonkey menu only)
     * ===================================================================== */
    /* live status button at the TOP of the Tampermonkey menu, only for the survey open in THIS tab */
    function setStatus(kind, entry, rec) {
        let label = '';
        const m = entry ? Math.max(0, Math.floor((Date.now() - entry.startedAt) / MIN)) : 0;
        if (kind === 'checking') label = '⏳ Survey detected • ' + m + 'm • checking…';
        else if (kind === 'fresh') label = '🟢 NEW survey • ' + m + 'm / ' + Math.round(FAST_MS / MIN) + 'm';
        else if (kind === 'repeat') label = '🔴 REPEAT survey (done ' + (rec ? fmtDate(rec.ts) : '?') + ')';
        statusKind = kind || null;
        if (label === statusLabel) return;
        statusLabel = label;
        registerMenu(true);
    }

    /* on-demand status check: nothing is shown on the page unless YOU press this menu item */
    function pageStatus() {
        const pk = extractProjectKey();
        const lk = linkKeyFromUrl(location.href);
        const ik = iframeKeys();
        const mine = loadActive().find(e => e.tabId === tabId) || null;
        const v = evaluate(mine, pk, lk, loadLocks(), loadLog(), ik);
        const lines = [];
        if (v.block) {
            lines.push('⛔ DUPLICATE: you completed this survey on ' + fmtDT(v.block.ts));
            lines.push('Allowed again after: ' + fmtDT(v.block.ts + LOCK_MS));
        } else if (mine && qCountOf(mine) >= MIN_QUESTIONS_FOR_FINAL) {
            lines.push('✅ NEW survey: no duplicate found.');
        } else if (mine) {
            lines.push('⏳ Not enough questions seen yet (' + qCountOf(mine) + '/' + MIN_QUESTIONS_FOR_FINAL + '). No duplicate so far.');
        } else {
            lines.push('ℹ️ No survey session detected on this page yet.');
        }
        if (mine) {
            const el = Date.now() - mine.startedAt;
            lines.push('Timer: ' + fmtDur(el) + (el < FAST_MS ? '  (under 12m: do not finish yet)' : '  (12m+ OK)'));
            lines.push('Started: ' + fmtDT(mine.startedAt));
        }
        alert(lines.join('\n'));
    }

    /* ---------- UPDATE CHECK (menu command) ----------
     * Runs in the background: downloads the script file as TEXT, reads only its @version line and
     * compares it with the installed version. The downloaded code is never executed.
     * If newer, the Tampermonkey update page opens by itself (Tampermonkey itself installs scripts;
     * a script cannot overwrite itself). */
    function cmpVer(a, b) {
        const pa = String(a).split('.').map(n => parseInt(n, 10) || 0);
        const pb = String(b).split('.').map(n => parseInt(n, 10) || 0);
        for (let i = 0; i < Math.max(pa.length, pb.length); i++) {
            const d = (pa[i] || 0) - (pb[i] || 0);
            if (d) return d > 0 ? 1 : -1;
        }
        return 0;
    }
    function checkForUpdate() {
        if (typeof GM_xmlhttpRequest !== 'function') { alert('Update check not available.'); return; }
        let cur = '0';
        try { cur = GM_info.script.version || '0'; } catch (e) {}
        notify('🔄 Argon', 'Checking for update…');
        GM_xmlhttpRequest({
            method: 'GET',
            url: SCRIPT_URL + '?t=' + Date.now(),
            anonymous: true, nocache: true, timeout: 20000, responseType: 'text',
            onload: (r) => {
                if (r.status !== 200) { notify('🔄 Argon', 'Update check failed (HTTP ' + r.status + ').'); return; }
                const head = String(r.responseText).slice(0, 5000);
                if (!/==UserScript==/.test(head)) { notify('🔄 Argon', 'Update check failed: not a userscript file.'); return; }
                const m = head.match(/@version\s+([0-9][0-9.]*)/);
                if (!m) { notify('🔄 Argon', 'Update check failed: no version found.'); return; }
                const remote = m[1];
                if (cmpVer(remote, cur) > 0) {
                    notify('⬆️ Argon update', 'New version v' + remote + ' found (you have v' + cur + '). Opening update…');
                    try { GM_openInTab(SCRIPT_URL, { active: true, insert: true, setParent: true }); }
                    catch (e) { notify('⬆️ Argon update', 'Could not open the update page.'); }
                } else {
                    notify('✅ Argon', 'You already have the latest version (v' + cur + ').');
                }
            },
            onerror: () => notify('🔄 Argon', 'Update check failed: network error.'),
            ontimeout: () => notify('🔄 Argon', 'Update check failed: timeout.')
        });
    }

    /* ---------- ADMIN-CONTROLLED BLOCK DURATION ---------- */
    function applyLockDays(n) {
        n = Number(n);
        if (!LOCK_CHOICES.includes(n)) n = 15;
        LOCK_DAYS = n;
        LOCK_MS = n * DAY;
    }
    function syncLockDays() {
        const r = gGet(ADMIN_KEY, null) || {};
        const n = LOCK_CHOICES.includes(Number(r.lockDays)) ? Number(r.lockDays) : 15;
        if (n !== LOCK_DAYS) { applyLockDays(n); registerMenu(true); }
    }

    /* ---------- USAGE REPORT: one async report every 6 hours (never blocks the page) ----------
     * Only records that the server has NOT confirmed yet are sent. The server updates the same user record
     * in place and appends the new survey rows under it (re-sent rows are matched by their ID, no duplicates).
     * Pending and Blocked IDs also report (so the admin can see them), but they have no survey rows. */
    let hbPauseUntil = 0, hbFails = 0;
    function getEmpName() {
        const n = gGet(NAME_KEY, '');
        return typeof n === 'string' ? n.slice(0, 40) : '';
    }
    function setMyName() {
        const cur = getEmpName();
        const v = prompt('Your employee name / ID (shown in the admin work report):', cur);
        if (v === null) return;
        const clean = v.replace(/[\u0000-\u001f]/g, ' ').trim().slice(0, 40);
        gSet(NAME_KEY, clean);
        alert(clean ? 'Saved: ' + clean : 'Name cleared.');
        hbPauseUntil = 0; hbFails = 0;
        try { sendTrack(); } catch (e) {}        // v13.6: the admin sees the name right away (no 6-hour wait)
    }
    /* ---------- v13.6: block diagnostics + admin unlock of a FALSE block ---------- */
    function scriptVersion() { try { return GM_info.script.version || '?'; } catch (e) { return '?'; } }
    function whyBlocked() {
        const pk = extractProjectKey() || '-', lk = linkKeyFromUrl(location.href) || '-';
        const locks = loadLocks(), log = loadLog();
        const L = [];
        L.push('Script version: ' + scriptVersion());
        L.push('Page project key: ' + pk);
        L.push('Page link key: ' + lk);
        L.push('Blocked now: ' + (blockActive ? 'YES' : 'no'));
        [pk, lk].forEach(k => {
            const r = locks[k];
            if (r) L.push('LOCK key: ' + k + '\n   done: ' + fmtDT(r.ts) + '  owner project (pk): ' + (r.pk || '(empty)') + '  host: ' + (r.h || '-'));
        });
        const hits = log.filter(r => r && ((r.projectKey === pk) || (r.altKeys || []).includes(pk) || (r.linkKey && r.linkKey === lk)));
        hits.slice(0, 3).forEach(r => L.push('LOG ROW done: ' + fmtDT(r.ts) + '\n   link: ' + String(r.link || '').slice(0, 90) + '\n   projectKey: ' + (r.projectKey || '(empty)') + '\n   altKeys: ' + (r.altKeys || []).join(', ')));
        if (blockActive && lastBlock && lastBlock.rec) L.push('Block came from a record done at ' + fmtDT(lastBlock.rec.ts) + ' (owner pk: ' + (lastBlock.rec.pk || '(empty)') + ')');
        if (!locks[pk] && !locks[lk] && !hits.length && blockActive) L.push('No direct key match -> the block came from QUESTION matching.');
        if (IS_UT) {
            const lq = tabGet('lastq'), ug = tabGet('utgone');
            L.push('UserTesting: last-question page seen: ' + (lq ? fmtDT(lq.ts) : 'no') + ' | progress bar gone since: ' + (ug ? fmtDT(ug.ts) : 'no'));
        }
        alert(L.join('\n'));
    }
    function adminUnlockHere() {
        if (!adminUnlocked()) { alert('Login first.'); return; }
        if (!blockActive || !lastBlock || !lastBlock.rec) { alert('This tab is not showing a repeat block.'); return; }
        const rec = lastBlock.rec, pk = extractProjectKey() || '', lk = linkKeyFromUrl(location.href) || '';
        if (!confirm('Unlock THIS survey only?\nProject: ' + (pk || lk || '?') + '\n(The survey that was really completed on ' + fmtDT(rec.ts) + ' stays locked.)')) return;
        mutateLocks(m => {
            Object.keys(m).forEach(k => {
                const r = m[k];
                if (!r) return;
                if (k === pk || k === lk) { delete m[k]; return; }
                if (r.ts === rec.ts && (k.startsWith('qo::') || k.startsWith('qq::'))) delete m[k];   // false question match
            });
        });
        mutateLog(a => {
            a.forEach(r => {
                if (!r || r.ts !== rec.ts) return;
                r.altKeys = (r.altKeys || []).filter(k => k !== pk && k !== lk);
                if (r.linkKey && r.linkKey === lk) r.linkKey = '';
                if (pk && r.projectKey === pk) r.unlocked = true;
            });
        });
        clearBlock();
        scheduleScan(200);
        alert('Unlocked. If the red screen is still there, reload the page once.');
    }
    /* ADMIN: lock a survey by pasting its link (fixes a wrong / missing record by hand) */
    function adminUnlockRemote() {
        if (!adminUnlocked()) { alert('Login first.'); return; }
        const a = prompt('Unlock a survey for a USER.\nPaste the survey LINK, or the Survey key shown on the red screen (id::decipher::53b/261000):');
        if (!a) return;
        let pk = a.trim();
        if (/^https?:/i.test(pk)) pk = projectKeyFromHref(pk) || linkKeyFromUrl(pk) || '';
        pk = pk.toLowerCase();
        if (!/^(id|lk)::.{3,290}$/.test(pk)) { alert('No survey ID found.'); return; }
        const idRaw = prompt('Access ID of that user (shown on the red screen).\nLeave EMPTY = unlock for EVERY user:', '');
        if (idRaw === null) return;
        const id = idRaw.trim().toLowerCase();
        if (id && !ID_RE.test(id)) { alert('Invalid Access ID.'); return; }
        if (!confirm('UNLOCK ' + pk + '\nFor: ' + (id || 'EVERY user') + '\n\nOnly locks made BEFORE now are cleared. A new completion later locks again.')) return;
        publishChange(cur => {
            const now = Date.now();
            let u = Array.isArray(cur.unlocks) ? cur.unlocks : [];
            u = u.filter(x => x && Number.isFinite(Number(x.ts)) && now - Number(x.ts) < 31 * DAY && !(x.pk === pk && (x.id || '') === id));
            u.push({ pk: pk, id: id, ts: now });
            cur.unlocks = u.slice(-500);
        });
    }
    function adminLockLink() {
        if (!adminUnlocked()) { alert('Login first.'); return; }
        const raw = prompt('Paste the survey link that you COMPLETED:');
        if (!raw) return;
        let u;
        try { u = new URL(raw.trim()); } catch (e) { alert('Not a valid link.'); return; }
        const pk = projectKeyFromHref(u.href) || '', lk = linkKeyFromUrl(u.href) || '';
        if (!pk && !lk) { alert('No survey / project ID found in this link.'); return; }
        const tsRaw = prompt('When did you complete it?  Format: YYYY-MM-DD HH:MM  (empty = now)', '');
        let ts = Date.now();
        if (tsRaw && tsRaw.trim()) {
            const t = new Date(tsRaw.trim().replace(' ', 'T')).getTime();
            if (!Number.isFinite(t) || t > Date.now() + 60000) { alert('Invalid date.'); return; }
            ts = t;
        }
        if (Date.now() - ts >= LOCK_MS) { alert('That date is older than the lock time (' + LOCK_DAYS + ' days). Nothing to lock.'); return; }
        if (!confirm('LOCK this survey as completed?\n' + (pk || lk) + '\nDone: ' + fmtDT(ts) + '\nBlocked until: ' + fmtDT(ts + LOCK_MS))) return;
        const keys = [pk, lk].filter(Boolean), dom = u.hostname.toLowerCase();
        addLocks(keys, 'completed', ts, pk, dom);
        mutateLog(a => {
            a.push({ id: 'm_' + Date.now().toString(36) + Math.random().toString(36).slice(2, 6), ts: ts, start: null, end: ts, durMs: null,
                     link: u.href.slice(0, 1000), linkKey: lk, domain: dom, projectKey: pk, altKeys: keys, source: 'Admin manual', status: 'Completed' });
        });
        registerMenu(true);
        alert('Locked: ' + (pk || lk));
    }
    function askNameOnce() {
        try {
            if (!TRACK_URL || getEmpName() || gGet(NAME_ASKED_KEY, false)) return;
            gSet(NAME_ASKED_KEY, true);
            setMyName();
            registerMenu(true);
        } catch (e) {}
    }
    function restoreAccessId() {
        const raw = prompt('Type your OLD Access ID (ask the admin) to restore it.\nCurrent ID: ' + getClientId());
        if (!raw) return;
        const v = raw.trim().toLowerCase();
        if (!ID_RE.test(v)) { alert('Invalid ID format.'); return; }
        if (!confirm('Use Access ID ' + v + ' on this browser?')) return;
        gSet(CLIENT_ID_KEY, v);
        gSet(NAME_SENT_KEY, '');
        hbPauseUntil = 0; hbFails = 0;
        try { refreshAdminList(true); } catch (e) {}
        try { applyGate(); } catch (e) {}
        registerMenu(true);
        try { sendTrack(); } catch (e) {}
        alert('Access ID restored: ' + v);
    }
    /* survey records not yet confirmed by the server (15 min overlap so a later Lootwalls correction is re-sent) */
    function pendingRows() {
        const since = (Number(gGet(SYNC_KEY, 0)) || 0) - 15 * MIN;
        return loadLog().filter(r => Number(r.ts) > since).sort((a, b) => a.ts - b.ts);
    }
    /* domain + project ID + times only. No full URL, no questions, no answers. */
    function rowPayload(r) {
        return {
            rid: String(r.id || '').slice(0, 40),
            day: dateKey(Number(r.end || r.ts)),
            s: Number(r.start) || 0,
            e: Number(r.end || r.ts) || 0,
            dur: typeof r.durMs === 'number' ? Math.round(r.durMs) : -1,
            dom: String(r.domain || '').slice(0, 80),
            pk: String(r.projectKey || '').slice(0, 80),
            st: String(r.status || 'Completed').slice(0, 40),
            src: String(r.source || '').slice(0, 40)
        };
    }
    function buildPayload(rows) {
        let ver = '';
        try { ver = GM_info.script.version || ''; } catch (e) {}
        const now = Date.now();
        const st = licenseStatus();
        return {
            id: getClientId(), ver: ver, name: getEmpName(),
            lic: st === 'active' ? 'ok' : st,        // ok | pending | blocked
            working: st === 'active' && loadActive().some(e => now - e.updatedAt < 10 * MIN),
            rows: rows.map(rowPayload)
        };
    }
    function sendTrack() {
        if (!TRACK_URL || typeof GM_xmlhttpRequest !== 'function') return;
        const now = Date.now();
        if (now < hbPauseUntil) return;
        const last = Number(gGet(HB_KEY, 0)) || 0;
        const nameDirty = getEmpName() !== String(gGet(NAME_SENT_KEY, ''));
        if (now - last < HEARTBEAT_MS && !(nameDirty && now - last > 20 * 1000)) return;   // not due yet, unless the name is not on the server yet
        gSet(HB_KEY, now);
        const all = pendingRows();
        const batch = all.slice(0, TRACK_MAX_ROWS);
        const sentMax = batch.length ? Number(batch[batch.length - 1].ts) : 0;
        const more = all.length > batch.length;
        const fail = () => {
            hbFails++;
            const wait = Math.min(30 * MIN, Math.pow(2, hbFails) * MIN);
            hbPauseUntil = Date.now() + wait;
            gSet(HB_KEY, Date.now() - HEARTBEAT_MS + wait);     // retry after the back-off, not after 6 hours
        };
        const go = () => {
            try {
                const sentName = getEmpName();
                GM_xmlhttpRequest({
                    method: 'POST',
                    url: TRACK_URL.replace(/\/+$/, '') + '/hb',
                    headers: { 'Content-Type': 'application/json', 'X-Argon-Key': TRACK_INGEST_KEY },
                    data: JSON.stringify(buildPayload(batch)),
                    anonymous: true, timeout: 15000,
                    onload: (r) => {
                        if (r.status >= 200 && r.status < 300) {
                            hbFails = 0;
                            gSet(NAME_SENT_KEY, sentName);
                            if (sentMax) gSet(SYNC_KEY, Math.max(sentMax, Number(gGet(SYNC_KEY, 0)) || 0));
                            if (more) gSet(HB_KEY, Date.now() - HEARTBEAT_MS + 2 * MIN);   // more pending: continue in 2 min
                        } else fail();
                    },
                    onerror: fail, ontimeout: fail
                });
            } catch (e) { fail(); }
        };
        if (typeof window.requestIdleCallback === 'function') window.requestIdleCallback(go, { timeout: 3000 });
        else setTimeout(go, 0);
    }
    function trackInit() {
        if (!TRACK_URL) return;
        setTimeout(sendTrack, 4000 + Math.floor(Math.random() * 4000));   // browser opened: report if 6h passed
        setInterval(sendTrack, 60 * 1000);                                 // browser stays open: report every 6h
    }
    function trackInfo() {
        if (!TRACK_URL) { alert('Usage reporting: OFF'); return; }
        const pend = pendingRows();
        const last = Number(gGet(HB_KEY, 0)) || 0;
        alert('Usage reporting: ON (every 6 hours)\n' +
              'Access status of this browser: ' + licenseStatus().toUpperCase() + '\n' +
              'Last report: ' + (last ? fmtDT(last) : 'never') + '\n' +
              'Next report: ' + (last ? fmtDT(last + HEARTBEAT_MS) : 'soon') + '\n' +
              'Survey records waiting to be sent: ' + pend.length + '\n\nExample of what is sent:\n' +
              JSON.stringify(buildPayload(pend.slice(0, 1)), null, 1) +
              '\n\nNOT sent: full page URLs, survey questions or answers.\nNothing is stored in your browser except two timestamps and your name.');
    }

    function trackAdminGet(path, cb) {
        const t = gGet(TRACK_TOKEN_KEY, '');
        if (!TRACK_URL) { cb(0, null, 'TRACK_URL is not set in the script.'); return; }
        if (!t) { cb(0, null, 'No tracking admin token. Use "ADMIN: Set tracking token" first.'); return; }
        GM_xmlhttpRequest({
            method: 'GET',
            url: TRACK_URL.replace(/\/+$/, '') + path,
            headers: { 'Authorization': 'Bearer ' + t },
            anonymous: true, nocache: true, timeout: 20000, responseType: 'text',
            onload: r => cb(r.status, r.responseText, ''),
            onerror: () => cb(0, null, 'Network error.'),
            ontimeout: () => cb(0, null, 'Timeout.')
        });
    }
    function trackErr(st, err) {
        if (err) { alert(err); return true; }
        if (st === 401 || st === 403) { alert('Server refused the token (HTTP ' + st + ').'); return true; }
        if (st !== 200) { alert('Server error HTTP ' + st); return true; }
        return false;
    }
    function adminSetTrackToken() {
        if (!adminUnlocked()) { alert('Login first.'); return; }
        const t = prompt('Paste the tracking ADMIN token (stored only in this browser):');
        if (!t) return;
        gSet(TRACK_TOKEN_KEY, t.trim());
        alert('Tracking token saved in this browser only.');
    }
    function adminLiveUsers() {
        if (!adminUnlocked()) { alert('Login first.'); return; }
        trackAdminGet('/live', (st, txt, err) => {
            if (trackErr(st, err)) return;
            let j; try { j = JSON.parse(txt); } catch (e) { alert('Bad server response.'); return; }
            const rows = Array.isArray(j.rows) ? j.rows : [];
            const now = Date.now();
            alert('Reported in the last 7 hours: ' + rows.length + '\n(reports come every 6h, so this is not second-by-second)\n\n' + rows.slice(0, 60).map(r =>
                (r.name ? r.name + ' ' : '') + '[' + r.id + ']  •  ' + accessStatusOf(r.id) + '  •  last report ' + Math.max(0, Math.round((now - r.last_seen) / MIN)) + 'm ago  •  ' +
                (r.working ? 'was WORKING' : 'was idle')).join('\n'));
        });
    }
    /* ---------- minimal .xlsx writer (no library, no eval): stored ZIP + inline strings ---------- */
    const CRC_T = (function () {
        const t = new Uint32Array(256);
        for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = (c & 1) ? (0xEDB88320 ^ (c >>> 1)) : (c >>> 1); t[n] = c >>> 0; }
        return t;
    })();
    function crc32(b) { let c = 0xFFFFFFFF; for (let i = 0; i < b.length; i++) c = CRC_T[(c ^ b[i]) & 255] ^ (c >>> 8); return (c ^ 0xFFFFFFFF) >>> 0; }
    function xmlEsc(v) {
        return String(v).replace(/[\u0000-\u0008\u000b\u000c\u000e-\u001f]/g, '').replace(/[&<>"]/g, ch => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[ch]));
    }
    function colName(i) { let s = '', n = i + 1; while (n > 0) { const m = (n - 1) % 26; s = String.fromCharCode(65 + m) + s; n = Math.floor((n - 1) / 26); } return s; }
    function sheetXml(rows) {
        const widths = [];
        rows.forEach(r => r.forEach((v, i) => { widths[i] = Math.min(60, Math.max(widths[i] || 8, String(v == null ? '' : v).length + 2)); }));
        let x = '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><worksheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main">' +
            '<sheetViews><sheetView workbookViewId="0"><pane ySplit="1" topLeftCell="A2" activePane="bottomLeft" state="frozen"/></sheetView></sheetViews><cols>' +
            widths.map((w, i) => '<col min="' + (i + 1) + '" max="' + (i + 1) + '" width="' + w + '" customWidth="1"/>').join('') + '</cols><sheetData>';
        rows.forEach((r, ri) => {
            x += '<row r="' + (ri + 1) + '">';
            r.forEach((v, ci) => {
                const ref = colName(ci) + (ri + 1), st = ri === 0 ? ' s="1"' : '';
                if (typeof v === 'number' && Number.isFinite(v)) x += '<c r="' + ref + '"' + st + '><v>' + v + '</v></c>';
                else x += '<c r="' + ref + '"' + st + ' t="inlineStr"><is><t xml:space="preserve">' + xmlEsc(v == null ? '' : v) + '</t></is></c>';
            });
            x += '</row>';
        });
        return x + '</sheetData></worksheet>';
    }
    function zipStore(files) {
        const enc = new TextEncoder(), chunks = [], central = [];
        const u16 = v => [v & 255, (v >>> 8) & 255], u32 = v => [v & 255, (v >>> 8) & 255, (v >>> 16) & 255, (v >>> 24) & 255];
        let off = 0;
        files.forEach(f => {
            const name = enc.encode(f.name), data = enc.encode(f.data), crc = crc32(data);
            const lh = [].concat(u32(0x04034b50), u16(20), u16(0x0800), u16(0), u16(0), u16(0x21), u32(crc), u32(data.length), u32(data.length), u16(name.length), u16(0));
            chunks.push(new Uint8Array(lh), name, data);
            central.push(new Uint8Array([].concat(u32(0x02014b50), u16(20), u16(20), u16(0x0800), u16(0), u16(0), u16(0x21), u32(crc),
                u32(data.length), u32(data.length), u16(name.length), u16(0), u16(0), u16(0), u16(0), u32(0), u32(off))), name);
            off += lh.length + name.length + data.length;
        });
        let cdSize = 0; central.forEach(c => { cdSize += c.length; });
        const end = new Uint8Array([].concat(u32(0x06054b50), u16(0), u16(0), u16(files.length), u16(files.length), u32(cdSize), u32(off), u16(0)));
        const all = chunks.concat(central, [end]);
        let total = 0; all.forEach(c => { total += c.length; });
        const out = new Uint8Array(total); let p = 0;
        all.forEach(c => { out.set(c, p); p += c.length; });
        return out;
    }
    function makeXlsx(sheets) {      // sheets: [{ name, rows: [[...], ...] }]  (first row = header)
        const n = sheets.length;
        const files = [
            { name: '[Content_Types].xml', data: '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types"><Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/><Default Extension="xml" ContentType="application/xml"/><Override PartName="/xl/workbook.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet.main+xml"/><Override PartName="/xl/styles.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.styles+xml"/>' +
                sheets.map((x, i) => '<Override PartName="/xl/worksheets/sheet' + (i + 1) + '.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.worksheet+xml"/>').join('') + '</Types>' },
            { name: '_rels/.rels', data: '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships"><Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" Target="xl/workbook.xml"/></Relationships>' },
            { name: 'xl/workbook.xml', data: '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><workbook xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships"><sheets>' +
                sheets.map((x, i) => '<sheet name="' + xmlEsc(x.name) + '" sheetId="' + (i + 1) + '" r:id="rId' + (i + 1) + '"/>').join('') + '</sheets></workbook>' },
            { name: 'xl/_rels/workbook.xml.rels', data: '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">' +
                sheets.map((x, i) => '<Relationship Id="rId' + (i + 1) + '" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/worksheet" Target="worksheets/sheet' + (i + 1) + '.xml"/>').join('') +
                '<Relationship Id="rId' + (n + 1) + '" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/styles" Target="styles.xml"/></Relationships>' },
            { name: 'xl/styles.xml', data: '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><styleSheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main"><fonts count="2"><font><sz val="11"/><name val="Calibri"/></font><font><b/><sz val="11"/><name val="Calibri"/></font></fonts><fills count="2"><fill><patternFill patternType="none"/></fill><fill><patternFill patternType="gray125"/></fill></fills><borders count="1"><border><left/><right/><top/><bottom/><diagonal/></border></borders><cellStyleXfs count="1"><xf numFmtId="0" fontId="0" fillId="0" borderId="0"/></cellStyleXfs><cellXfs count="2"><xf numFmtId="0" fontId="0" fillId="0" borderId="0" xfId="0"/><xf numFmtId="0" fontId="1" fillId="0" borderId="0" xfId="0" applyFont="1"/></cellXfs></styleSheet>' }
        ];
        sheets.forEach((x, i) => files.push({ name: 'xl/worksheets/sheet' + (i + 1) + '.xml', data: sheetXml(x.rows) }));
        return zipStore(files);
    }
    const XLSX_MIME = 'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet';

    /* access status of an ID according to the admin list this browser holds (refreshed right before every export) */
    function accessStatusOf(id) {
        const lic = licenseInfo();
        if (lic.blocked.includes(id)) return 'Blocked';
        if (lic.active.includes(id)) return 'Allowed';
        return lic.enforce ? 'Pending' : 'Open (license check OFF)';
    }
    function reportedLic(v) {
        return v === 'ok' ? 'Allowed' : v === 'pending' ? 'Pending' : v === 'blocked' ? 'Blocked' : 'Not allowed (old script)';
    }

    /* one export for any time window -> ONE Excel file with three sheets:
       "Employee Summary" (one row per employee), "Survey Details" (survey rows grouped under each employee, oldest first)
       and "New Users" (access IDs that joined inside the window) */
    function adminExport(fromMs, toMs, label) {
        trackAdminGet('/export?from=' + fromMs + '&to=' + toMs, (st, txt, err) => {
            if (trackErr(st, err)) return;
            let j; try { j = JSON.parse(txt); } catch (e) { alert('Bad server response.'); return; }
            const us = Array.isArray(j.users) ? j.users : [], sv = Array.isArray(j.surveys) ? j.surveys : [], nu = Array.isArray(j.newUsers) ? j.newUsers : [];
            if (!us.length && !sv.length && !nu.length) { alert('No data for this period.'); return; }
            const period = fmtDT(fromMs) + '  to  ' + fmtDT(toMs);
            const r1 = [['SL', 'Period', 'Employee', 'User ID', 'Completed surveys', 'Too fast (<12m)', 'Total survey time (min)', 'Avg per survey (min)', 'First survey', 'Last survey', 'Last report received', 'Reports (total)', 'Script version', 'Access (as reported)', 'Access (now)']];
            us.forEach((r, i) => r1.push([
                i + 1, period, r.name || '', r.id, Number(r.done) || 0, Number(r.fast) || 0, Math.round(r.dur_ms / MIN * 10) / 10,
                r.timed ? Math.round(r.dur_ms / r.timed / MIN * 10) / 10 : '',
                r.first_done ? fmtDT(r.first_done) : '', r.last_done ? fmtDT(r.last_done) : '',
                r.last_seen ? fmtDT(r.last_seen) : '', Number(r.reports) || 0, r.ver || '', reportedLic(r.lic), accessStatusOf(r.id)
            ]));
            const r2 = [['SL', 'Date', 'Employee', 'User ID', 'Start', 'End', 'Duration (min)', 'Speed Check (12m)', 'Status', 'Survey domain', 'Project ID', 'Verified by']];
            sv.forEach((r, i) => {
                const known = r.dur_ms >= 0;
                r2.push([
                    i + 1, r.day || '', r.name || '', r.id, r.start_ts ? fmtDT(r.start_ts) : '', fmtDT(r.end_ts),
                    known ? Math.round(r.dur_ms / MIN * 10) / 10 : '', !known ? 'UNKNOWN' : (r.dur_ms < FAST_MS ? 'RED (<12m)' : 'OK (12m+)'),
                    r.status || '', r.domain || '', r.pk || '', r.src || ''
                ]);
            });
            const r3 = [['SL', 'Access ID', 'Employee', 'First seen', 'Last report', 'Script version', 'Access (now)']];
            nu.forEach((r, i) => r3.push([i + 1, r.id, r.name || '', r.first_seen ? fmtDT(r.first_seen) : '', r.last_seen ? fmtDT(r.last_seen) : '', r.ver || '', accessStatusOf(r.id)]));
            const bytes = makeXlsx([{ name: 'Employee Summary', rows: r1 }, { name: 'Survey Details', rows: r2 }, { name: 'New Users', rows: r3 }]);
            downloadBlob(bytes, XLSX_MIME, 'employee_report_' + label + '.xlsx');
        });
    }
    function adminDownload24h() {
        if (!adminUnlocked()) { alert('Login first.'); return; }
        const to = Date.now();
        refreshAdminList(true, () => adminExport(to - DAY, to + 60000, 'last24h_' + dateKey(to) + '_' + pad2(new Date(to).getHours()) + pad2(new Date(to).getMinutes())));
    }
    function adminDownloadDay() {
        if (!adminUnlocked()) { alert('Login first.'); return; }
        const d = (prompt('Date to download (YYYY-MM-DD):', dateKey(Date.now())) || '').trim();
        const m = d.match(/^(\d{4})-(\d{2})-(\d{2})$/);
        if (!m) { if (d) alert('Invalid date.'); return; }
        const from = new Date(+m[1], +m[2] - 1, +m[3]).getTime();
        const to = new Date(+m[1], +m[2] - 1, +m[3] + 1).getTime();
        refreshAdminList(true, () => adminExport(from, to, d));
    }
    /* separate file: ONLY the access IDs that joined in the last 24 hours */
    function adminDownloadNewIds() {
        if (!adminUnlocked()) { alert('Login first.'); return; }
        const to = Date.now(), from = to - DAY;
        refreshAdminList(true, () => {
            trackAdminGet('/new?from=' + from + '&to=' + (to + 60000), (st, txt, err) => {
                if (trackErr(st, err)) return;
                let j; try { j = JSON.parse(txt); } catch (e) { alert('Bad server response.'); return; }
                const nu = Array.isArray(j.users) ? j.users : [];
                if (!nu.length) { alert('No new Access ID in the last 24 hours.'); return; }
                const rows = [['SL', 'Access ID', 'First seen', 'Last report', 'Access (now)']];
                nu.forEach((r, i) => rows.push([i + 1, r.id, r.first_seen ? fmtDT(r.first_seen) : '', r.last_seen ? fmtDT(r.last_seen) : '', accessStatusOf(r.id)]));
                downloadBlob(makeXlsx([{ name: 'New Access IDs', rows: rows }]), XLSX_MIME,
                    'new_access_ids_' + dateKey(to) + '_' + pad2(new Date(to).getHours()) + pad2(new Date(to).getMinutes()) + '.xlsx');
            });
        });
    }
    function adminSetLockDays(n) {
        if (!adminUnlocked()) { alert('Login first.'); return; }
        if (!LOCK_CHOICES.includes(n)) return;
        if (!confirm('Set the repeat-block time to ' + n + ' days for ALL users?')) return;
        publishChange(cur => {
            if (Number(cur.lockDays) === n) { alert('Already ' + n + ' days.'); return false; }
            cur.lockDays = n;
        });
    }

    function registerMenu(force) {
        if (typeof GM_registerMenuCommand !== 'function') return;
        const n = todaysRows().length;
        const adm = adminUnlocked();
        const st = licenseStatus();
        if (!force && n === menuCount && statusLabel === menuStatus && adm === menuAdm && st === menuLic) return;
        if (typeof GM_unregisterMenuCommand === 'function') {
            menuIds.forEach(id => { try { GM_unregisterMenuCommand(id); } catch (e) {} });
        } else if (menuIds.length) {
            return;
        }
        menuIds = [];
        menuCount = n;
        menuStatus = statusLabel;
        menuAdm = adm;
        menuLic = st;
        const cmd = (label, fn) => menuIds.push(GM_registerMenuCommand(label, fn));
        const active = st === 'active';
        const cid = getClientId();

        if (!active) {
            // Pending / Blocked: no feature, only the state line, the ID, name, usage info, update and admin login
            const line = st === 'blocked'
                ? '⛔ BLOCKED by admin: all features are off'
                : '🟡 PENDING: waiting for admin approval (features are off)';
            cmd(line, () => alert(line + '\n\n' + (getEmpName() ? 'Name: ' + getEmpName() + '\n' : '') + 'Your Access ID: ' + cid + '\n\nGive this ID to the admin.' +
                (st === 'pending' ? '\nAfter approval the features start within about 5-10 minutes.' : '')));
        } else {
            // registered FIRST so it appears above the sheet buttons
            if (statusLabel) cmd(statusLabel, pageStatus);
            cmd('📥 Download today\'s spreadsheet (' + n + ')', () => {
                const rows = todaysRows();
                if (!rows.length) { alert('No completed survey recorded today.'); return; }
                downloadRows(rows, 'completed_surveys_' + dateKey(Date.now()) + '.csv');
            });
            cmd('📥 Download last ' + LOCK_DAYS + ' days', () => {
                const since = Date.now() - LOCK_DAYS * DAY;
                const rows = loadLog().filter(r => r.ts >= since).sort((a, b) => a.ts - b.ts);
                if (!rows.length) { alert('No completed survey in the last ' + LOCK_DAYS + ' days.'); return; }
                downloadRows(rows, 'completed_surveys_last_' + LOCK_DAYS + '_days.csv');
            });
            cmd('📥 Download everything saved', () => {
                const rows = loadLog().sort((a, b) => a.ts - b.ts);
                if (!rows.length) { alert('Nothing saved yet.'); return; }
                downloadRows(rows, 'completed_surveys_all.csv');
            });
            cmd('💾 Backup (JSON: locks + log)', () => {
                const data = { v: 12, exportedAt: Date.now(), locks: gGet(LOCKS_KEY, {}), log: gGet(LOG_KEY, []) };
                downloadBlob(JSON.stringify(data, null, 1), 'application/json;charset=utf-8;', 'argon_backup_' + dateKey(Date.now()) + '.json');
            });
            cmd('📤 Import backup (merge from other browser)', importBackup);
        }
        cmd('ℹ️ Argon version ' + scriptVersion() + ' (running now)', () => alert('Running version: ' + scriptVersion() + '\nIf you see this script TWICE in the Tampermonkey dashboard, delete the old copy.'));
        if (active) cmd('🔍 Why is this page blocked?', whyBlocked);
        cmd('⬆️ Check for script update', checkForUpdate);
        cmd('ℹ️ Usage reporting info', trackInfo);
        if (TRACK_URL) cmd('👤 Set my name / employee ID' + (getEmpName() ? ' (' + getEmpName() + ')' : ' (not set)'), () => { setMyName(); registerMenu(true); });

        if (active || adm) {
            const ar = gGet(ADMIN_KEY, null);
            const lbl = ar ? '🛡️ Admin list v' + ar.v + ' (' + (ar.domains || []).length + ' domains, ' + (ar.keywords || []).length + ' keywords)' : '🛡️ Admin list: not downloaded yet';
            cmd(lbl, () => alert(lbl));
        }
        cmd('🔄 Refresh admin list now', () => refreshAdminList(true, (m) => alert(m)));
        {
            const lic = licenseInfo();
            const stTxt = st === 'active' ? (lic.enforce ? 'Active ✅' : 'Active, license check OFF') : st === 'blocked' ? 'BLOCKED ❌' : 'PENDING 🟡';
            const nmv = getEmpName();
            cmd('👤 ' + (nmv ? 'Name: ' + nmv : 'Name NOT set (click to set)'), () => { setMyName(); registerMenu(true); });
            const lbl = '🔑 Access ID: ' + cid + ' (' + stTxt + ')';
            cmd(lbl, () => alert((nmv ? 'Name: ' + nmv + '\n' : '') + lbl));
            cmd('♻️ Restore my old Access ID', restoreAccessId);
        }
        if (adm) {
            const lic = licenseInfo();
            cmd('🔓 ADMIN: Unlock this survey (false block)', adminUnlockHere);
            cmd('🔒 ADMIN: Lock a completed survey (paste link)', adminLockLink);
            cmd('🌐 ADMIN: Unlock a survey for a USER (remote)', adminUnlockRemote);
            cmd('➕ ADMIN: Add domain', () => adminAddRule('d'));
            cmd('➕ ADMIN: Add keyword', () => adminAddRule('k'));
            cmd('➖ ADMIN: Remove rule', adminRemoveRule);
            cmd('💬 ADMIN: Set block message', adminSetMessage);
            cmd('📋 ADMIN: View all rules', adminViewRules);
            cmd('🔑 ADMIN: Set GitHub token', adminSetToken);
            cmd('🟡 ADMIN: Pending IDs (new users)', () => openLicensePanel('pending'));
            cmd('🟢 ADMIN: Admin Allow List (' + lic.active.length + ')', () => openLicensePanel('allow'));
            cmd('🔴 ADMIN: Admin Block List (' + lic.blocked.length + ')', () => openLicensePanel('block'));
            cmd('🔁 ADMIN: Toggle license enforcement (now ' + (lic.enforce ? 'ON' : 'OFF') + ')', adminToggleLicenseEnforce);
            cmd('✅ ADMIN: Allow an ID by typing it', adminActivateId);
            cmd('❌ ADMIN: Remove an ID from both lists', adminRevokeId);
            cmd('📋 ADMIN: View license list', adminViewLicense);
            LOCK_CHOICES.forEach(k => cmd(
                (LOCK_DAYS === k ? '✅ ' : '🗓️ ') + 'ADMIN: Repeat block ' + k + ' days' + (LOCK_DAYS === k ? ' (current)' : ''),
                () => adminSetLockDays(k)));
            cmd('👥 ADMIN: Live users', adminLiveUsers);
            cmd('📥 ADMIN: Download last 24 hours (one Excel file)', adminDownload24h);
            cmd('📥 ADMIN: Download a chosen day (one Excel file)', adminDownloadDay);
            cmd('📥 ADMIN: New Access IDs only (24h, separate Excel)', adminDownloadNewIds);
            cmd('🔑 ADMIN: Set tracking token', adminSetTrackToken);
            cmd('🚪 ADMIN: Logout', adminLogout);
        } else {
            cmd('🔐 Admin login', adminLogin);
        }
    }

    /* =====================================================================
     * ADMIN BLOCKLIST (local + remote JSON, data only)
     * ===================================================================== */
    let adminBlocked = false, adminHostEl = null, adminHit = null, adminHref = '';
    let curStatus = 'pending', linkTick = 0;

    const ID_RE = /^[a-f0-9]{8,20}$/;

    function cleanList(a, kind) {
        if (!Array.isArray(a)) return [];
        const out = [];
        for (const x of a.slice(0, 3000)) {
            if (typeof x !== 'string') continue;
            let s = x.trim().toLowerCase();
            if (kind === 'd') {
                s = s.replace(/^https?:\/\//, '').replace(/^www\./, '').split('/')[0];
                if (!/^[a-z0-9-]+(\.[a-z0-9-]+)+$/.test(s)) continue;
            } else if (s.length < 4 || s.length > 100) continue;   // too-short keywords could block everything
            if (!out.includes(s)) out.push(s);
        }
        return out;
    }
    function cleanIds(a) {
        if (!Array.isArray(a)) return [];
        const out = [];
        for (const x of a) {
            if (typeof x !== 'string') continue;
            const s = x.trim().toLowerCase();
            if (ID_RE.test(s) && !out.includes(s)) out.push(s);
            if (out.length >= 2000) break;
        }
        return out;
    }
    function cleanUnlocks(a) {
        const out = [];
        if (!Array.isArray(a)) return out;
        for (const x of a.slice(0, 600)) {
            if (!x || typeof x.pk !== 'string') continue;
            const pk = x.pk.trim().toLowerCase().slice(0, 300);
            const id = (typeof x.id === 'string' && ID_RE.test(x.id.trim().toLowerCase())) ? x.id.trim().toLowerCase() : '';
            const ts = Number(x.ts);
            if (!/^(id|lk)::/.test(pk) || !Number.isFinite(ts)) continue;
            out.push({ pk: pk, id: id, ts: ts });
        }
        return out;
    }
    function adminUnlockList() { const r = gGet(ADMIN_KEY, null) || {}; return Array.isArray(r.unlocks) ? r.unlocks : []; }
    function cleanNames(o) {
        const out = {};
        if (!o || typeof o !== 'object' || Array.isArray(o)) return out;
        let n = 0;
        for (const k of Object.keys(o)) {
            if (++n > 3000) break;
            const id = String(k).trim().toLowerCase();
            if (!ID_RE.test(id) || typeof o[k] !== 'string') continue;
            const v = o[k].replace(/[\u0000-\u001f]/g, ' ').trim().slice(0, 40);
            if (v) out[id] = v;
        }
        return out;
    }
    function parseAdminList(text) {
        let d;
        try { d = JSON.parse(text); } catch (e) { return null; }
        if (!d || typeof d !== 'object') return null;
        const lic = (d.license && typeof d.license === 'object') ? d.license : {};
        return {
            v: Number(d.version) || 0,
            msg: typeof d.message === 'string' ? d.message.slice(0, 300) : '',
            domains: cleanList(d.domains, 'd'),
            keywords: cleanList(d.keywords, 'k'),
            license: {
                enforce: !!lic.enforce,
                active: cleanIds(lic.active),
                blocked: cleanIds(lic.blocked),
                names: cleanNames(lic.names)
            },
            unlocks: cleanUnlocks(d.unlocks),
            lockDays: LOCK_CHOICES.includes(Number(d.lockDays)) ? Number(d.lockDays) : 15,
            fetchedAt: Date.now()
        };
    }
    function adminRules() {
        const r = gGet(ADMIN_KEY, null) || {};
        return {
            v: r.v || 0,
            msg: r.msg || '',
            domains: BUILTIN_BLOCK.domains.concat(r.domains || []),
            keywords: BUILTIN_BLOCK.keywords.concat(r.keywords || [])
        };
    }

    /* ---------- ACCESS STATUS: active / pending / blocked ---------- */
    function licenseInfo() {
        const r = gGet(ADMIN_KEY, null) || {};
        const l = (r.license && typeof r.license === 'object') ? r.license : {};
        return {
            enforce: !!l.enforce,
            active: Array.isArray(l.active) ? l.active : [],
            blocked: Array.isArray(l.blocked) ? l.blocked : [],
            names: (l.names && typeof l.names === 'object' && !Array.isArray(l.names)) ? l.names : {}
        };
    }
    function getClientId() {
        let id = gGet(CLIENT_ID_KEY, null);
        if (id && typeof id === 'string') return id;
        id = Array.from(crypto.getRandomValues(new Uint8Array(6))).map(b => b.toString(16).padStart(2, '0')).join('');
        gSet(CLIENT_ID_KEY, id);
        return id;
    }
    function licenseStatus() {
        if (FAIL_CLOSED_NO_LIST && !gGet(ADMIN_KEY, null)) return 'pending';   // admin list never downloaded yet
        const lic = licenseInfo(), id = getClientId();
        if (lic.blocked.includes(id)) return 'blocked';                        // blocked wins, whatever "enforce" says
        if (!lic.enforce) return 'active';
        return lic.active.includes(id) ? 'active' : 'pending';
    }

    /* admin block rules (domain / keyword) against ONE url */
    function matchAdmin(urlStr, rules) {
        try {
            const u = new URL(urlStr);
            const h = u.hostname.toLowerCase();
            if (hostInList(h, NON_SURVEY_HOSTS)) return null;      // safety: never block google, github etc.
            rules = rules || adminRules();
            const d = rules.domains.find(x => h === x || h.endsWith('.' + x));
            if (d) return { type: 'domain', rule: d, msg: rules.msg };
            const full = decodeSafe(urlStr).toLowerCase();
            const k = rules.keywords.find(x => full.includes(x));
            if (k) return { type: 'keyword', rule: k, msg: rules.msg };
        } catch (e) {}
        return null;
    }

    /* ---------- LINK SCAN: every <a href> in the page (v13.4) ---------- */
    function linkPageBlockAllowed() {
        return LINK_BLOCK_PAGE && (LINK_PAGE_BLOCK_ON_ROUTERS || !(isRouterDomain || hostIs('lootwalls.com')));
    }
    function scanLinksIn(roots) {
        const rules = adminRules();
        if (!rules.domains.length && !rules.keywords.length) return null;
        let n = 0;
        for (const r of roots) {
            let as;
            try { as = r.querySelectorAll('a[href]'); } catch (e) { continue; }
            for (const a of as) {
                if (++n > LINK_SCAN_MAX) return null;
                const href = a.href;
                if (typeof href !== 'string' || !/^https?:/i.test(href)) continue;
                const hit = matchAdmin(href, rules);
                if (hit) return { type: 'link ' + hit.type, rule: hit.rule, msg: hit.msg };
            }
        }
        return null;
    }
    /* a CLICK on a matching link is always stopped (left, middle, keyboard Enter); nothing is added to the page */
    let clickBlockInstalled = false;
    function installLinkClickBlock() {
        if (clickBlockInstalled) return;
        clickBlockInstalled = true;
        const handler = (ev) => {
            if (!gateOpen) return;
            try {
                const path = ev.composedPath ? ev.composedPath() : [ev.target];
                let a = null;
                for (const el of path) {
                    if (el && el.tagName && String(el.tagName).toUpperCase() === 'A' && typeof el.href === 'string' && el.href) { a = el; break; }
                }
                if (!a || !/^https?:/i.test(a.href)) return;
                const hit = matchAdmin(a.href);
                if (!hit) return;
                ev.preventDefault();
                ev.stopImmediatePropagation();
                notify('🚫 Link blocked by admin', 'Matched ' + hit.type + ': ' + hit.rule);
            } catch (e) {}
        };
        ['click', 'auxclick'].forEach(t => document.addEventListener(t, handler, true));
    }

    function matchAdminAny() {
        let hit = matchAdmin(location.href);
        if (hit) return hit;
        try {
            const frames = document.querySelectorAll('iframe[src]');
            for (const f of frames) {
                if (!/^https?:/i.test(f.src)) continue;
                const r = f.getBoundingClientRect();
                if (r.width < IFRAME_MIN_W || r.height < IFRAME_MIN_H) continue;
                hit = matchAdmin(f.src);
                if (hit) return hit;
            }
        } catch (e) {}
        if (linkPageBlockAllowed() && document.body) {
            // light scan (main document) every time, deep scan (shadow DOM + same-origin iframes) every ~10 s,
            // and always deep while a link block is showing so the screen does not flicker
            const deep = (adminBlocked && adminHit && /^link/.test(adminHit.type)) || (++linkTick % 5 === 0);
            try { hit = scanLinksIn(deep ? collectRoots() : [document]); } catch (e) { hit = null; }
            if (hit) return hit;
        }
        return null;
    }
    function removeAdminBlock() {
        adminBlocked = false; adminHit = null;
        if (adminHostEl) { try { adminHostEl.remove(); } catch (e) {} adminHostEl = null; }
        scheduleScan(300);
    }
    function renderAdminBlock() {
        if (!adminBlocked || !document.documentElement) return;
        if (adminHostEl && adminHostEl.isConnected) return;
        adminHostEl = document.createElement('div');
        adminHostEl.style.cssText = 'all:initial;';
        const root = adminHostEl.attachShadow({ mode: 'closed' });
        const wrap = mk('div', 'position:fixed;top:0;left:0;width:100%;height:100%;background:#5c0a12;z-index:2147483647;display:flex;align-items:center;justify-content:center;font-family:sans-serif;color:#fff;text-align:center;padding:20px;box-sizing:border-box;');
        const card = mk('div', 'background:rgba(0,0,0,0.55);padding:28px;border-radius:12px;max-width:560px;width:100%;border:2px solid #ff4d4d;');
        card.appendChild(mk('h2', 'margin:0 0 12px;color:#ffeb3b;font-size:20px;line-height:1.3;', '🚫 This survey is BLOCKED by admin'));
        card.appendChild(mk('p', 'font-size:15px;line-height:1.5;margin:0 0 10px;',
            (adminHit && adminHit.msg) ? adminHit.msg : 'This survey / router is on the prohibited list. Do not take it.'));
        if (adminHit) card.appendChild(mk('div', 'font-size:12px;opacity:.8;margin:8px 0 14px;word-break:break-all;', 'Matched ' + adminHit.type + ': ' + adminHit.rule));
        const btn = mk('button', 'background:#ffeb3b;color:#000;border:none;padding:12px 26px;border-radius:6px;font-weight:bold;cursor:pointer;font-size:15px;', 'Exit');
        btn.onclick = () => {
            try { window.close(); } catch (e) {}
            setTimeout(() => { try { location.replace('about:blank'); } catch (e) {} }, 200);
        };
        card.appendChild(btn);
        wrap.appendChild(card);
        root.appendChild(wrap);
        document.documentElement.appendChild(adminHostEl);
    }
    function adminCheck() {
        if (!gateOpen) return;
        if (adminBlocked) {
            if (location.href !== adminHref) {            // page changed inside the same tab
                adminHref = location.href;
                const again = matchAdminAny();
                if (!again) { removeAdminBlock(); return; }
                adminHit = again;
            } else if (!matchAdminAny()) {                // rule was removed by admin meanwhile
                removeAdminBlock();
                return;
            }
            if (!adminHostEl || !adminHostEl.isConnected) renderAdminBlock();
            return;
        }
        const hit = matchAdminAny();
        if (!hit) return;
        adminBlocked = true;
        adminHit = hit;
        adminHref = location.href;
        try { window.stop(); } catch (e) {}
        if (blockActive) clearBlock();
        renderAdminBlock();
        onReady(renderAdminBlock);
        notify('🚫 Blocked by admin', 'Matched ' + hit.type + ': ' + hit.rule);
    }

    /* ---------- RED SCREEN of a BLOCKED Access ID ---------- */
    function removeLicenseBlock() {
        if (licHostEl) { try { licHostEl.remove(); } catch (e) {} licHostEl = null; }
    }
    function renderLicenseBlock() {
        if (curStatus !== 'blocked' || BLOCKED_SCREEN !== 'all' || !document.documentElement) return;
        if (licHostEl && licHostEl.isConnected) return;
        licHostEl = document.createElement('div');
        licHostEl.style.cssText = 'all:initial;';
        const root = licHostEl.attachShadow({ mode: 'closed' });
        const wrap = mk('div', 'position:fixed;top:0;left:0;width:100%;height:100%;background:#5c0a12;z-index:2147483647;display:flex;align-items:center;justify-content:center;font-family:sans-serif;color:#fff;text-align:center;padding:20px;box-sizing:border-box;');
        const card = mk('div', 'background:rgba(0,0,0,0.55);padding:28px;border-radius:12px;max-width:560px;width:100%;border:2px solid #ff4d4d;');
        card.appendChild(mk('h2', 'margin:0 0 12px;color:#ffeb3b;font-size:20px;line-height:1.3;', '⛔ Your Access ID is blocked by admin'));
        card.appendChild(mk('p', 'font-size:15px;line-height:1.5;margin:0 0 8px;', 'আপনার Access ID অ্যাডমিন ব্লক করেছে। এই এক্সটেনশনের কোনো ফিচার চলবে না।'));
        card.appendChild(mk('div', 'font:13px monospace;opacity:.9;margin:8px 0 14px;word-break:break-all;', (getEmpName() ? 'Name: ' + getEmpName() + '  |  ' : '') + 'Access ID: ' + getClientId()));
        const btn = mk('button', 'background:#ffeb3b;color:#000;border:none;padding:12px 26px;border-radius:6px;font-weight:bold;cursor:pointer;font-size:15px;', 'Close tab');
        btn.onclick = () => { try { window.close(); } catch (e) {} };
        card.appendChild(btn);
        wrap.appendChild(card);
        root.appendChild(wrap);
        document.documentElement.appendChild(licHostEl);
    }
    function stateNotify(st) {
        const last = Number(gGet(NOTIFY_KEY, 0)) || 0;
        const gap = st === 'blocked' ? 10 * MIN : 12 * HOUR;
        if (Date.now() - last < gap) return;
        gSet(NOTIFY_KEY, Date.now());
        if (st === 'blocked') notify('⛔ Argon: Access ID blocked', 'The admin blocked your Access ID ' + getClientId() + '. All features are off.');
        else notify('🟡 Argon: waiting for approval', (getEmpName() ? getEmpName() + ' | ' : '') + 'Access ID ' + getClientId() + '. Give it to the admin. Features start after approval.');
    }

    /* ---------- THE GATE: features run ONLY while the Access ID is active ---------- */
    function applyGate() {
        const st = licenseStatus();
        curStatus = st;
        if (st === 'active') {
            gateOpen = true;
            removeLicenseBlock();
            startFeatures();
        } else {
            const wasOpen = gateOpen;
            gateOpen = false;
            if (wasOpen) {                                   // features were running: switch them off now
                if (blockActive) clearBlock();
                if (adminBlocked) removeAdminBlock();
            }
            if (st === 'blocked') {
                if (BLOCKED_SCREEN === 'all') onReady(renderLicenseBlock);
                else stateNotify(st);
            } else {
                removeLicenseBlock();
                stateNotify(st);
            }
        }
        registerMenu(false);
    }

    function refreshAdminList(force, cb) {
        if (typeof GM_xmlhttpRequest !== 'function' || !REMOTE_LIST_URL) { if (cb) cb('Remote list not available.'); return; }
        const cur = gGet(ADMIN_KEY, null);
        const now = Date.now();
        if (!force) {
            if (cur && now - (cur.fetchedAt || 0) < REMOTE_REFRESH_MS) return;
            if (now - Number(gGet(ADMIN_KEY + '_try', 0)) < 60000) return;   // avoid many tabs fetching together
        }
        gSet(ADMIN_KEY + '_try', now);
        GM_xmlhttpRequest({
            method: 'GET',
            url: REMOTE_LIST_URL + (REMOTE_LIST_URL.includes('?') ? '&' : '?') + 't=' + now,
            anonymous: true, nocache: true, timeout: 15000, responseType: 'text',
            onload: (r) => {
                let msg = 'Download failed (HTTP ' + r.status + '). Old list kept.';
                if (r.status === 200 && String(r.responseText).length < 500000) {
                    const p = parseAdminList(r.responseText);
                    if (p) {
                        const oldU = JSON.stringify((cur && cur.unlocks) || []);
                        gSet(ADMIN_KEY, p);
                        applyLockDays(p.lockDays);
                        if (blockActive && JSON.stringify(p.unlocks || []) !== oldU) { clearBlock(); scheduleScan(300); }
                        msg = 'Admin list updated: v' + p.v + ', ' + p.domains.length + ' domains, ' + p.keywords.length + ' keywords.';
                        applyGate();
                        adminCheck();
                        registerMenu(true);
                    } else msg = 'Invalid list file. Old list kept.';
                }
                if (cb) cb(msg);
            },
            onerror: () => { if (cb) cb('Network error. Old list kept.'); },
            ontimeout: () => { if (cb) cb('Timeout. Old list kept.'); }
        });
    }

    /* =====================================================================
     * ADMIN LOGIN + PUBLISH (password = salted hash check, publish = GitHub API with YOUR token)
     * ===================================================================== */
    function sha256hex(str) {
        const msg = unescape(encodeURIComponent(str));
        const rr = (v, a) => (v >>> a) | (v << (32 - a));
        const K = [], H = [];
        let pc = 0;
        const isP = {};
        for (let c = 2; pc < 64; c++) {
            if (!isP[c]) {
                for (let i = 0; i < 313; i += c) isP[i] = c;
                if (pc < 8) H[pc] = (Math.pow(c, 1 / 2) * 4294967296) | 0;
                K[pc++] = (Math.pow(c, 1 / 3) * 4294967296) | 0;
            }
        }
        const bytes = [];
        for (let i = 0; i < msg.length; i++) bytes.push(msg.charCodeAt(i));
        const bitLen = bytes.length * 8;
        bytes.push(0x80);
        while (bytes.length % 64 !== 56) bytes.push(0);
        const hi = Math.floor(bitLen / 4294967296), lo = bitLen >>> 0;
        [hi, lo].forEach(x => { for (let s = 24; s >= 0; s -= 8) bytes.push((x >>> s) & 255); });
        for (let off = 0; off < bytes.length; off += 64) {
            const w = [];
            for (let i = 0; i < 16; i++) w[i] = (bytes[off + 4 * i] << 24) | (bytes[off + 4 * i + 1] << 16) | (bytes[off + 4 * i + 2] << 8) | (bytes[off + 4 * i + 3]);
            for (let i = 16; i < 64; i++) {
                const s0 = rr(w[i - 15], 7) ^ rr(w[i - 15], 18) ^ (w[i - 15] >>> 3);
                const s1 = rr(w[i - 2], 17) ^ rr(w[i - 2], 19) ^ (w[i - 2] >>> 10);
                w[i] = (w[i - 16] + s0 + w[i - 7] + s1) | 0;
            }
            let [a, b, c, d, e, f, g, h] = H;
            for (let i = 0; i < 64; i++) {
                const S1 = rr(e, 6) ^ rr(e, 11) ^ rr(e, 25);
                const ch = (e & f) ^ (~e & g);
                const t1 = (h + S1 + ch + K[i] + w[i]) | 0;
                const S0 = rr(a, 2) ^ rr(a, 13) ^ rr(a, 22);
                const maj = (a & b) ^ (a & c) ^ (b & c);
                const t2 = (S0 + maj) | 0;
                h = g; g = f; f = e; e = (d + t1) | 0; d = c; c = b; b = a; a = (t1 + t2) | 0;
            }
            const v = [a, b, c, d, e, f, g, h];
            for (let i = 0; i < 8; i++) H[i] = (H[i] + v[i]) | 0;
        }
        return H.map(x => ('00000000' + (x >>> 0).toString(16)).slice(-8)).join('');
    }

    function adminUnlocked() {
        const s = tabGet('adm');
        return !!(s && Date.now() - s.ts < ADMIN_SESSION_MS);
    }
    function adminLogin() {
        const f = gGet(ADMIN_FAIL_KEY, { n: 0, until: 0 });
        if (Date.now() < f.until) { alert('Too many wrong attempts. Try again later.'); return; }
        const p = prompt('Admin password:');
        if (p === null) return;
        if (sha256hex(ADMIN_SALT + p) === ADMIN_PASS_HASH) {
            gSet(ADMIN_FAIL_KEY, { n: 0, until: 0 });
            tabSet('adm', { ts: Date.now() });
            registerMenu(true);
            alert('Admin unlocked for ' + Math.round(ADMIN_SESSION_MS / MIN) + ' minutes (this tab).');
        } else {
            f.n++;
            if (f.n >= 5) { f.until = Date.now() + 10 * MIN; f.n = 0; }
            gSet(ADMIN_FAIL_KEY, f);
            alert('Wrong password.');
        }
    }
    function adminLogout() { tabSet('adm', undefined); closePanel(); registerMenu(true); }

    function ghApi(method, bodyObj, cb) {
        const token = gGet(TOKEN_KEY, '');
        if (!token) { cb(0, null, 'No GitHub token set. Use "ADMIN: Set GitHub token" first.'); return; }
        GM_xmlhttpRequest({
            method: method,
            url: 'https://api.github.com/repos/' + GH_OWNER + '/' + GH_REPO + '/contents/' + GH_PATH + (method === 'GET' ? '?ref=' + GH_BRANCH : ''),
            headers: {
                'Authorization': 'Bearer ' + token,
                'Accept': 'application/vnd.github+json',
                'Content-Type': 'application/json'
            },
            data: bodyObj ? JSON.stringify(bodyObj) : undefined,
            anonymous: true, nocache: true, timeout: 20000, responseType: 'text',
            onload: r => cb(r.status, r.responseText, ''),
            onerror: () => cb(0, null, 'Network error.'),
            ontimeout: () => cb(0, null, 'Timeout.')
        });
    }
    /* downloads the CURRENT file, applies your change, uploads it back (so nothing is overwritten).
       opts.onEnd(ok, message): when given, the result goes there (used by the Allow / Block window) instead of alert(). */
    function publishChange(mutator, opts) {
        opts = opts || {};
        const end = (ok, msg) => {
            if (opts.onEnd) { try { opts.onEnd(ok, msg || ''); } catch (e) {} }
            else if (msg) alert(msg);
        };
        if (!adminUnlocked()) { end(false, 'Admin session expired. Login again.'); registerMenu(true); return; }
        ghApi('GET', null, (st, txt, err) => {
            if (err) { end(false, err); return; }
            if (st === 401 || st === 403) { end(false, 'GitHub refused the token (HTTP ' + st + '). Check token permission.'); return; }
            if (st === 404) { end(false, 'File ' + GH_PATH + ' not found in the repo. Create it first.'); return; }
            if (st !== 200) { end(false, 'GitHub error HTTP ' + st); return; }
            let cur, sha;
            try {
                const j = JSON.parse(txt);
                sha = j.sha;
                let raw = '';
                try { raw = decodeURIComponent(escape(atob(String(j.content || '').replace(/\s/g, '')))); } catch (e) { raw = ''; }
                raw = raw.replace(/^\uFEFF/, '').trim();
                try { cur = raw ? JSON.parse(raw) : null; } catch (e) { cur = null; }
                if (!cur || typeof cur !== 'object' || Array.isArray(cur)) {
                    if (!confirm('The list file on GitHub is empty or not valid JSON.\nReplace it with a fresh list and continue?')) { end(false, ''); return; }
                    cur = {};
                }
            } catch (e) { end(false, 'Could not read the GitHub response.'); return; }
            cur.domains = Array.isArray(cur.domains) ? cur.domains : [];
            cur.keywords = Array.isArray(cur.keywords) ? cur.keywords : [];
            const note = mutator(cur);
            if (note === false) { end(false, ''); return; }
            cur.version = (Number(cur.version) || 0) + 1;
            const content = btoa(unescape(encodeURIComponent(JSON.stringify(cur, null, 2))));
            ghApi('PUT', { message: 'admin update v' + cur.version, content: content, sha: sha, branch: GH_BRANCH }, (st2, txt2, err2) => {
                if (err2) { end(false, err2); return; }
                if (st2 === 200 || st2 === 201) {
                    const p = parseAdminList(JSON.stringify(cur));
                    if (p) { gSet(ADMIN_KEY, p); applyLockDays(p.lockDays); }
                    applyGate();
                    adminCheck();
                    registerMenu(true);
                    end(true, 'Published v' + cur.version + '. All users get it within ~5-10 minutes. Domains: ' + cur.domains.length + ', Keywords: ' + cur.keywords.length);
                } else end(false, 'Publish failed (HTTP ' + st2 + ').' + (st2 === 409 ? ' The list changed meanwhile, try again.' : ''));
            });
        });
    }
    function adminAddRule(kind) {
        if (!adminUnlocked()) { alert('Login first.'); return; }
        const raw = prompt(kind === 'd' ? 'Domain to block (example: badsurvey.com):' : 'Keyword to block (min 4 letters, part of URL):');
        if (!raw) return;
        const v = cleanList([raw], kind)[0];
        if (!v) { alert('Invalid ' + (kind === 'd' ? 'domain' : 'keyword (min 4 chars)') + '.'); return; }
        if (kind === 'd' && hostInList(v, NON_SURVEY_HOSTS)) { alert('This domain is protected (never blocked).'); return; }
        publishChange(cur => {
            const arr = kind === 'd' ? cur.domains : cur.keywords;
            if (arr.includes(v)) { alert('Already in the list.'); return false; }
            arr.push(v);
        });
    }
    function adminRemoveRule() {
        if (!adminUnlocked()) { alert('Login first.'); return; }
        const raw = prompt('Domain or keyword to REMOVE from the list:');
        if (!raw) return;
        const v = raw.trim().toLowerCase();
        publishChange(cur => {
            const n1 = cur.domains.length, n2 = cur.keywords.length;
            cur.domains = cur.domains.filter(x => x !== v);
            cur.keywords = cur.keywords.filter(x => x !== v);
            if (cur.domains.length === n1 && cur.keywords.length === n2) { alert('Not found in the list.'); return false; }
        });
    }
    function adminSetMessage() {
        if (!adminUnlocked()) { alert('Login first.'); return; }
        const m = prompt('Message shown on the block screen:');
        if (m === null) return;
        publishChange(cur => { cur.message = m.slice(0, 300); });
    }
    function adminViewRules() {
        const r = adminRules();
        alert('Version: ' + r.v + '\nMessage: ' + (r.msg || '-') + '\n\nDOMAINS (' + r.domains.length + '):\n' + r.domains.slice(0, 80).join('\n') +
            '\n\nKEYWORDS (' + r.keywords.length + '):\n' + r.keywords.slice(0, 80).join('\n'));
    }
    function adminSetToken() {
        if (!adminUnlocked()) { alert('Login first.'); return; }
        const t = prompt('Paste your GitHub fine-grained token (stored only in this browser).\nIt must have access ONLY to the DATA repo "' + GH_REPO + '" (Contents: Read and write):');
        if (!t) return;
        gSet(TOKEN_KEY, t.trim());
        alert('Token saved in this browser only.');
    }

    /* ---------- ACCESS LIST CHANGES (Allow / Block / Unblock / Remove) ---------- */
    /* allow   : ID -> Allow list (removed from Block list)
       block   : ID -> Block list (removed from Allow list)
       unblock : ID leaves the Block list and goes back to PENDING (not straight to Active)
       remove  : ID leaves both lists (becomes PENDING) */
    function licenseMutate(act, id, cb, nm) {
        if (!ID_RE.test(id)) { cb(false, 'Invalid ID format.'); return; }
        if (id === getClientId() && act !== 'allow') { cb(false, 'This is your own admin browser. It cannot be blocked or removed from here.'); return; }
        publishChange(cur => {
            cur.license = (cur.license && typeof cur.license === 'object') ? cur.license : {};
            const L = cur.license;
            L.enforce = !!L.enforce;
            L.active = Array.isArray(L.active) ? L.active : [];
            L.blocked = Array.isArray(L.blocked) ? L.blocked : [];
            L.names = (L.names && typeof L.names === 'object' && !Array.isArray(L.names)) ? L.names : {};
            const before = JSON.stringify([L.active, L.blocked, L.names]);
            L.active = L.active.filter(x => x !== id);
            L.blocked = L.blocked.filter(x => x !== id);
            if (act === 'allow') L.active.push(id);
            else if (act === 'block') L.blocked.push(id);
            if (L.active.length > 2000 || L.blocked.length > 2000) { alert('List is full (max 2000).'); return false; }
            if (nm && (act === 'allow' || act === 'block')) L.names[id] = String(nm).replace(/[\u0000-\u001f]/g, ' ').trim().slice(0, 40);   // name is saved WITH the ID
            if (JSON.stringify([L.active, L.blocked, L.names]) === before) return false;      // nothing changed
        }, { onEnd: (ok, msg) => cb(ok, msg || (ok ? 'Done.' : 'No change.')) });
    }
    function adminToggleLicenseEnforce() {
        if (!adminUnlocked()) { alert('Login first.'); return; }
        const now = licenseInfo().enforce;
        const q = now
            ? 'Turn license enforcement OFF?\nEvery ID that is not blocked will get all features again.'
            : 'Turn license enforcement ON?\nEvery ID that is NOT in the Allow list becomes PENDING and loses ALL features within ~5-10 minutes.\nAllow your existing employees first.';
        if (!confirm(q)) return;
        publishChange(cur => {
            cur.license = (cur.license && typeof cur.license === 'object') ? cur.license : {};
            cur.license.active = Array.isArray(cur.license.active) ? cur.license.active : [];
            cur.license.blocked = Array.isArray(cur.license.blocked) ? cur.license.blocked : [];
            cur.license.enforce = !cur.license.enforce;
        });
    }
    function adminActivateId() {
        if (!adminUnlocked()) { alert('Login first.'); return; }
        const raw = prompt('Access ID to ALLOW:');
        if (!raw) return;
        const v = raw.trim().toLowerCase();
        if (!ID_RE.test(v)) { alert('Invalid ID format.'); return; }
        if (!confirm('ALLOW ID ' + v + '?')) return;
        licenseMutate('allow', v, (ok, msg) => alert(msg));
    }
    function adminRevokeId() {
        if (!adminUnlocked()) { alert('Login first.'); return; }
        const raw = prompt('Access ID to REMOVE from both lists (it becomes Pending):');
        if (!raw) return;
        const v = raw.trim().toLowerCase();
        if (!ID_RE.test(v)) { alert('Invalid ID format.'); return; }
        if (!confirm('REMOVE ID ' + v + ' from both lists?')) return;
        licenseMutate('remove', v, (ok, msg) => alert(msg));
    }
    function adminViewLicense() {
        const lic = licenseInfo();
        alert('Enforce: ' + (lic.enforce ? 'ON' : 'OFF') + '\n\nALLOWED IDs (' + lic.active.length + '):\n' + lic.active.slice(0, 100).join('\n') +
            '\n\nBLOCKED IDs (' + lic.blocked.length + '):\n' + lic.blocked.slice(0, 100).join('\n'));
    }

    /* ---------- ONE WINDOW, THREE VIEWS: Pending IDs / Admin Allow List / Admin Block List ---------- */
    function closePanel() {
        if (panelHost) { try { panelHost.remove(); } catch (e) {} panelHost = null; }
    }
    function openLicensePanel(kind) {
        if (!adminUnlocked()) { alert('Login first.'); return; }
        if (!document.documentElement) { alert('Page is not ready yet.'); return; }
        closePanel();
        const TITLES = { pending: '🟡 Pending IDs (waiting for approval)', allow: '🟢 Admin Allow List', block: '🔴 Admin Block List' };
        const EMPTY = {
            pending: 'No pending ID. (Only IDs that reported in the last 30 days are listed.)',
            allow: 'The Allow list is empty.',
            block: 'The Block list is empty.'
        };
        const me = getClientId();
        let users = {}, busy = false;

        panelHost = document.createElement('div');
        panelHost.style.cssText = 'all:initial;';
        const root = panelHost.attachShadow({ mode: 'closed' });
        const wrap = mk('div', 'position:fixed;top:0;left:0;width:100%;height:100%;background:rgba(0,0,0,.75);z-index:2147483647;display:flex;align-items:center;justify-content:center;font-family:sans-serif;padding:12px;box-sizing:border-box;');
        const card = mk('div', 'background:#fff;color:#111;padding:16px;border-radius:12px;max-width:780px;width:100%;box-sizing:border-box;max-height:92vh;display:flex;flex-direction:column;');
        card.appendChild(mk('h3', 'margin:0 0 6px;font-size:17px;color:#111;', TITLES[kind]));
        const note = mk('div', 'font-size:13px;min-height:18px;margin:0 0 8px;font-weight:600;color:#333;word-break:break-word;', 'Loading…');
        card.appendChild(note);
        const list = mk('div', 'overflow:auto;flex:1;border-top:1px solid #ddd;');
        card.appendChild(list);
        const foot = mk('div', 'display:flex;gap:10px;justify-content:flex-end;margin-top:10px;flex-wrap:wrap;');
        const btnCss = (bg, fg) => 'background:' + bg + ';color:' + fg + ';border:none;padding:8px 14px;border-radius:6px;font-weight:bold;cursor:pointer;font-size:13px;';
        const refreshBtn = mk('button', btnCss('#ddd', '#000'), 'Reload');
        refreshBtn.onclick = () => { if (!busy) load(); };
        const closeBtn = mk('button', btnCss('#333', '#fff'), 'Close');
        closeBtn.onclick = closePanel;
        foot.appendChild(refreshBtn);
        foot.appendChild(closeBtn);
        card.appendChild(foot);
        wrap.appendChild(card);
        root.appendChild(wrap);
        document.documentElement.appendChild(panelHost);

        const setNote = (msg, ok) => {
            note.textContent = msg;
            note.style.color = ok === true ? '#0a7a35' : ok === false ? '#b02a37' : '#333';
        };
        function doAction(act, id) {
            if (busy) return;
            const what = { allow: 'ALLOW', block: 'BLOCK', unblock: 'UNBLOCK (the ID goes back to Pending)', remove: 'REMOVE from the list (the ID becomes Pending)' }[act];
            if (!confirm(what + '\n\nAccess ID: ' + id + (((users[id] && users[id].name) || licenseInfo().names[id]) ? '\nName: ' + ((users[id] && users[id].name) || licenseInfo().names[id]) : ''))) return;
            busy = true;
            setNote('Publishing…');
            licenseMutate(act, id, (ok, msg) => {
                busy = false;
                render();
                setNote(msg, ok);
            }, (users[id] && users[id].name) || '');
        }
        function render() {
            list.textContent = '';
            const lic = licenseInfo();
            let ids;
            if (kind === 'allow') ids = lic.active.slice();
            else if (kind === 'block') ids = lic.blocked.slice();
            else ids = Object.keys(users).filter(id => !lic.active.includes(id) && !lic.blocked.includes(id));
            ids.sort((a, b) => ((users[b] && users[b].last_seen) || 0) - ((users[a] && users[a].last_seen) || 0));
            const nameOf = (id) => ((users[id] && users[id].name) || lic.names[id] || '');
            const allowedByName = {};
            lic.active.forEach(a => { const n = nameOf(a).toLowerCase(); if (n) allowedByName[n] = a; });
            if (!ids.length) { list.appendChild(mk('div', 'padding:16px;font-size:13px;color:#555;', EMPTY[kind])); return; }
            ids.forEach(id => {
                const u = users[id] || {};
                const row = mk('div', 'display:flex;gap:10px;align-items:center;justify-content:space-between;flex-wrap:wrap;padding:10px 4px;border-bottom:1px solid #eee;');
                const info = mk('div', 'min-width:0;flex:1 1 260px;');
                const nm = nameOf(id);
                info.appendChild(mk('div', 'font-size:15px;font-weight:700;word-break:break-word;color:#111;', (nm || '(no name)') + (id === me ? '   (this browser)' : '')));
                info.appendChild(mk('div', 'font:12px monospace;color:#333;word-break:break-all;', id));
                const oldId = (kind === 'pending' && nm) ? allowedByName[nm.toLowerCase()] : '';
                if (oldId && oldId !== id) info.appendChild(mk('div', 'font-size:12px;color:#b25e00;font-weight:600;', '⚠ Same name as Allowed ID ' + oldId + ' (probably a re-install). Allow this one, then Remove the old one.'));
                info.appendChild(mk('div', 'font-size:11px;color:#666;', 'First seen: ' + (u.first_seen ? fmtDT(u.first_seen) : '-') + '   |   Last report: ' + (u.last_seen ? fmtDT(u.last_seen) : '-')));
                row.appendChild(info);
                const btns = mk('div', 'display:flex;gap:6px;flex-wrap:wrap;');
                const add = (label, bg, fg, act, disabled) => {
                    const b = mk('button', btnCss(bg, fg) + (disabled ? 'opacity:.35;cursor:not-allowed;' : ''), label);
                    b.disabled = !!disabled;
                    b.onclick = () => doAction(act, id);
                    btns.appendChild(b);
                };
                if (kind === 'pending') { add('Allow', '#1e7e34', '#fff', 'allow'); add('Block', '#b02a37', '#fff', 'block', id === me); }
                else if (kind === 'allow') { add('Block', '#b02a37', '#fff', 'block', id === me); add('Remove', '#ddd', '#000', 'remove', id === me); }
                else { add('Unblock', '#1e7e34', '#fff', 'unblock'); add('Remove', '#ddd', '#000', 'remove'); }
                row.appendChild(btns);
                list.appendChild(row);
            });
        }
        function load() {
            setNote('Loading…');
            refreshAdminList(true, () => {
                trackAdminGet('/users?days=30', (st, txt, err) => {
                    let msg = '', ok = true;
                    if (err || st !== 200) {
                        ok = false;
                        msg = (err || (st === 401 || st === 403 ? 'Server refused the token (HTTP ' + st + ').' : 'Server error HTTP ' + st)) +
                              (kind === 'pending' ? ' The Pending list needs the server.' : ' Names and times are not shown.');
                    } else {
                        try {
                            const j = JSON.parse(txt);
                            users = {};
                            (j.users || []).forEach(u => { if (u && ID_RE.test(String(u.id))) users[u.id] = u; });
                        } catch (e) { ok = false; msg = 'Bad server response.'; }
                    }
                    render();
                    if (ok) {
                        const lic = licenseInfo();
                        setNote(kind === 'pending' ? 'Enforcement is ' + (lic.enforce ? 'ON' : 'OFF') + '. Pending IDs: ' + list.children.length : 'Enforcement is ' + (lic.enforce ? 'ON' : 'OFF') + '.', undefined);
                        if (kind === 'pending' && list.children.length === 1 && !Object.keys(users).length) setNote('No data from the server yet.', undefined);
                    } else setNote(msg, false);
                });
            });
        }
        load();
    }

    /* =====================================================================
     * INIT
     * ===================================================================== */
    function onReady(fn) {
        if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', fn, { once: true });
        else fn();
    }

    function snapshotOnce() {
        try {
            if (gGet(BACKUP_KEY, null) !== null) return;
            const locks = gGet(LOCKS_KEY, null), log = gGet(LOG_KEY, null);
            if (locks === null && log === null) return;
            gSet(BACKUP_KEY, { ts: Date.now(), locks: locks, log: log });
        } catch (e) {}
    }

    /* everything below runs ONLY for an ACTIVE Access ID (started once, switched off by gateOpen if the ID is later blocked) */
    function startFeatures() {
        if (featuresStarted) return;
        featuresStarted = true;

        // admin blocklist (domain / keyword / links): runs on every site (also routers / lootwalls), BEFORE anything else
        try { adminCheck(); } catch (e) { dbg('admin check error', e); }
        onReady(() => { try { adminCheck(); } catch (e) {} });
        setInterval(() => { try { adminCheck(); } catch (e) {} }, 2000);
        installLinkClickBlock();

        if (hostIs('lootwalls.com')) {
            onReady(() => {
                lootwallsTick();
                setInterval(lootwallsTick, 1000);
            });
            return;
        }
        if (isRouterDomain) return;

        noteSeen();
        try { urlPrecheck(); } catch (e) { dbg('precheck error', e); }   // block BEFORE the page even renders
        observeRoots([document]);
        setInterval(pollTick, POLL_MS);
        window.addEventListener('popstate', () => { scheduleScan(200); try { urlPrecheck(); } catch (e) {} });
        window.addEventListener('hashchange', () => { scheduleScan(200); try { urlPrecheck(); } catch (e) {} });
        document.addEventListener('visibilitychange', () => {
            if (!document.hidden) { heartbeat(); scheduleScan(300); }
        });
        onReady(() => scheduleScan(300));
        dbg('features started v14.4', { tabId: tabId, host: host });
    }

    function start() {
        if (started) return;
        started = true;
        snapshotOnce();
        syncLockDays();
        registerMenu(true);
        document.addEventListener('visibilitychange', () => { if (!document.hidden) registerMenu(true); });

        refreshAdminList(false);
        try { trackInit(); } catch (e) { dbg('track init error', e); }
        onReady(() => setTimeout(askNameOnce, 4000));   // runs for Pending / Blocked too; separate from every survey rule
        setInterval(() => refreshAdminList(false), 5 * MIN);
        setInterval(() => { if (curStatus === 'blocked') renderLicenseBlock(); }, 2000);   // keeps the Blocked red screen on the page

        applyGate();      // active -> startFeatures() | pending / blocked -> no feature at all
        dbg('started v14.4', { tabId: tabId, host: host, status: curStatus });
    }

    function init() {
        loadTabData(function () {
            tabId = initTabId();
            start();
        });
    }

    init();
})();
