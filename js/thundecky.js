/*
 * ThunDecky（https://github.com/ThunFasky/ThunDecky）の Web 版。
 * pygame 版の 600×600 の画面構成・操作をそのまま canvas に描き直したもの。
 * Web では意味のない機能（フォルダ選択・曲ファイルの削除・ジャケット差し替え・閉じる）は外し、
 * 色はサイトに合わせている。曲は music/ フォルダに置く（music/tracks.json があればそれを優先）。
 */
(function () {
    'use strict';

    const canvas = document.getElementById('thundecky');
    if (!canvas || !canvas.getContext) return;
    const ctx = canvas.getContext('2d');

    // ===== 定数（元アプリの値をそのまま使う） =====
    const W = 600, H = 600;
    const ART_SIZE = 250;
    const FRAME_GAP = 5;
    const FRAME_WIDTH = 8;
    const TRACK_VOL_X = 52, TRACK_VOL_TOP = 150, TRACK_VOL_BOTTOM = 355;
    const MASTER_VOL_TOP = 405, MASTER_VOL_BOTTOM = 575;
    const VOLUME_MIN_PERCENT = 1, VOLUME_MAX_PERCENT = 100, TRACK_VOLUME_STEP = 0.1;
    const MASTER_VOLUME_MIN = 0, MASTER_VOLUME_MAX = 25;
    const MASTER_VOLUME_STEP = 0.25, MASTER_VOLUME_DRAG_STEP = 0.05;
    const VOLUME_SLIDER_CURVE = 2.0;
    const TRACK_VOLUME_WHEEL_STEP = 0.5, MASTER_VOLUME_WHEEL_STEP = 0.05;
    const PANEL_X = 450, LEFT_W = PANEL_X;
    const ART_CENTER = [230, 255];
    const V_SPACING = 230;
    const BORDER_WIDTH = 3;
    const ANIM_DURATION = 0.4, WHEEL_ANIM_DURATION = 0.22;
    const ACTION_COOLDOWN = 0.25;
    const SHADOW_OFFSET = 4;
    const SWIPE_SPACING = 230, SWIPE_THRESHOLD = 0.3, CLICK_MOVE_TOLERANCE = 8;
    const VIS_NUM_BARS = 24, VIS_MAX_LEN = 58, VIS_GAP_FROM_ART = 16;
    const VIS_ATTACK = 0.55, VIS_DECAY = 0.18;
    const DEFAULT_MASTER = 15;
    const AUDIO_EXT = /\.(mp3|m4a|aac|ogg|oga|opus|wav|flac|webm)$/i;
    const REPO_CONTENTS_API = 'https://api.github.com/repos/ThunFasky/ThunFaskyWebSite/contents/music';

    // ===== 色（サイトのオレンジと暗い紺に合わせる） =====
    const rootStyle = getComputedStyle(document.documentElement);
    const MAIN = parseColor(rootStyle.getPropertyValue('--orange')) || [255, 117, 24];
    const BG = [14, 19, 33];
    const SHADOW = [4, 6, 12];
    const PANEL_FILL = [8, 11, 20];
    const SUB_LINE = [62, 70, 92];
    const SEEK_TRACK = [70, 78, 98];
    const rgb = (c, a) => a === undefined ? `rgb(${c[0]},${c[1]},${c[2]})` : `rgba(${c[0]},${c[1]},${c[2]},${a})`;

    const FONT_UI = "MyScoreFont, 'Courier New', monospace";
    const FONT_TITLE = "CorporateLogo, 'Hiragino Kaku Gothic ProN', Meiryo, sans-serif";
    const REDUCE_MOTION = window.matchMedia('(prefers-reduced-motion: reduce)').matches;

    function parseColor(s) {
        const m = (s || '').trim().match(/^#([0-9a-f]{6})$/i);
        if (!m) return null;
        const n = parseInt(m[1], 16);
        return [(n >> 16) & 255, (n >> 8) & 255, n & 255];
    }

    // ===== 保存（閲覧者ごとの音量・ループ設定。使えない環境では保存しないだけ） =====
    const store = {
        get(key, fallback) {
            try { const v = localStorage.getItem('thundecky.' + key); return v === null ? fallback : JSON.parse(v); } catch (e) { return fallback; }
        },
        set(key, value) {
            try { localStorage.setItem('thundecky.' + key, JSON.stringify(value)); } catch (e) { /* 保存できなくても動作は続ける */ }
        }
    };

    // ===== 状態 =====
    let playlist = [];          // { src, title, art? }
    let currentIndex = 0;
    let loopOne = !!store.get('loopOne', false);
    let masterValue = clampMaster(store.get('master', DEFAULT_MASTER));
    let trackVolumeMap = store.get('trackVolume', {}) || {};
    let isPlaying = false, isPaused = false;
    let visualOffset = 0, isAnimating = false, animStart = 0, animTarget = 0, animTimer = 0, animDuration = ANIM_DURATION;
    let moveDirection = 0, playAfterAnimation = false;
    let lastActionTime = 0;
    let swiping = false, swipeStart = [0, 0], swipeMoved = false, resumeAfterScroll = false;
    let seeking = false, seekDragRatio = 0;
    let trackVolumeDragging = false, masterDragging = false;
    let titleScrollX = 0, lastTitle = '';
    let loaded = false;
    const visLevels = new Float32Array(VIS_NUM_BARS);

    // 当たり判定（描画のたびに更新）
    let playRect = null, seekRect = null, loopRect = null, trackVolRect = null, volRect = null;
    let topSlotRect = null, bottomSlotRect = null, currentArtRect = null;

    // ===== 音声（<audio> を Web Audio に通し、音量と周波数解析をする） =====
    const audio = new Audio();
    audio.preload = 'metadata';
    let audioCtx = null, gainNode = null, analyser = null, freqData = null;
    let bandPeaks = new Float32Array(VIS_NUM_BARS).fill(1e-6);

    function ensureAudioGraph() {
        if (audioCtx) {
            if (audioCtx.state === 'suspended') audioCtx.resume().catch(() => {});
            return;
        }
        const AC = window.AudioContext || window.webkitAudioContext;
        if (!AC) return;
        try {
            audioCtx = new AC();
            const source = audioCtx.createMediaElementSource(audio);
            gainNode = audioCtx.createGain();
            analyser = audioCtx.createAnalyser();
            analyser.fftSize = 2048;
            analyser.smoothingTimeConstant = 0;
            freqData = new Float32Array(analyser.frequencyBinCount);
            source.connect(analyser);           // 解析は音量に左右されない位置で取る（元アプリと同じく、表示の長さは後で音量に比例させる）
            source.connect(gainNode);
            gainNode.connect(audioCtx.destination);
            audio.volume = 1;
        } catch (e) {
            audioCtx = null; gainNode = null; analyser = null;
        }
        applyEffectiveVolume();
    }

    function applyEffectiveVolume() {
        const gain = Math.max(0, Math.min(1, (masterValue / MASTER_VOLUME_MAX) * getTrackVolume()));
        if (gainNode) gainNode.gain.value = gain;
        else { try { audio.volume = gain; } catch (e) { /* iOS などでは変更できない */ } }
    }

    audio.addEventListener('ended', () => {
        if (!isPlaying) return;
        if (loopOne) startAudio(currentIndex);
        else if (playlist.length) beginOffsetAnim(1, 1, true);
    });
    audio.addEventListener('pause', () => {
        // OS のメディアキーなど、プレイヤー外から止められたときも表示を合わせる
        if (isPlaying && !audio.ended && !isAnimating && !seeking) { isPlaying = false; isPaused = true; }
    });
    audio.addEventListener('play', () => { isPlaying = true; isPaused = false; });

    function currentTrack() { return playlist.length ? playlist[mod(currentIndex, playlist.length)] : null; }

    function startAudio(index, startPos) {
        if (!playlist.length) return;
        ensureAudioGraph();
        currentIndex = mod(index, playlist.length);
        const track = playlist[currentIndex];
        const url = new URL(track.src, location.href).href;
        if (audio.src !== url) audio.src = url;
        applyEffectiveVolume();
        const seekTo = startPos || 0;
        const doPlay = () => {
            try { audio.currentTime = seekTo; } catch (e) { /* メタデータ前は後で合わせる */ }
            const p = audio.play();
            if (p && p.catch) p.catch(() => { isPlaying = false; isPaused = false; });
        };
        if (audio.readyState >= 1) doPlay();
        else audio.addEventListener('loadedmetadata', doPlay, { once: true });
        isPlaying = true; isPaused = false;
    }

    function stopAudioPlayback() {
        const wasPlaying = isPlaying;
        isPlaying = false; isPaused = false;
        audio.pause();
        return wasPlaying;
    }

    function togglePlay() {
        if (!playlist.length) return;
        if (isPlaying) {
            isPlaying = false; isPaused = true;
            audio.pause();
        } else if (isPaused) {
            ensureAudioGraph();
            isPlaying = true; isPaused = false;
            const p = audio.play();
            if (p && p.catch) p.catch(() => { isPlaying = false; isPaused = true; });
        } else {
            startAudio(currentIndex);
        }
    }

    // ===== 音量（スライダー位置 ⇔ 値。下側ほど小音量を細かく動かせるカーブ） =====
    function clampMaster(v) {
        let raw = Number(v);
        if (!isFinite(raw)) raw = DEFAULT_MASTER;
        raw = Math.max(MASTER_VOLUME_MIN, Math.min(raw, MASTER_VOLUME_MAX));
        return Math.round(raw / MASTER_VOLUME_DRAG_STEP) * MASTER_VOLUME_DRAG_STEP;
    }
    function clampTrackPercent(p) {
        let v = Number(p);
        if (!isFinite(v)) v = VOLUME_MAX_PERCENT;
        v = Math.round(Math.round(v / TRACK_VOLUME_STEP) * TRACK_VOLUME_STEP * 10) / 10;
        return Math.max(VOLUME_MIN_PERCENT, Math.min(v, VOLUME_MAX_PERCENT));
    }
    const sliderRatioToValue = (r, vmin, vmax) => vmin + (vmax - vmin) * Math.pow(Math.max(0, Math.min(r, 1)), VOLUME_SLIDER_CURVE);
    const valueToSliderRatio = (v, vmin, vmax) => Math.pow(Math.max(0, Math.min((v - vmin) / (vmax - vmin), 1)), 1 / VOLUME_SLIDER_CURVE);
    function getTrackVolumePercent() {
        const t = currentTrack();
        return t ? clampTrackPercent(trackVolumeMap[t.src] ?? VOLUME_MAX_PERCENT) : VOLUME_MAX_PERCENT;
    }
    const getTrackVolume = () => getTrackVolumePercent() / VOLUME_MAX_PERCENT;
    function setMaster(v) { masterValue = clampMaster(v); applyEffectiveVolume(); store.set('master', masterValue); }
    function setTrackVolume(p) {
        const t = currentTrack(); if (!t) return;
        trackVolumeMap[t.src] = clampTrackPercent(p);
        applyEffectiveVolume();
    }
    function setMasterFromY(y) {
        const ratio = 1 - Math.max(0, Math.min((y - MASTER_VOL_TOP) / (MASTER_VOL_BOTTOM - MASTER_VOL_TOP), 1));
        setMaster(sliderRatioToValue(ratio, MASTER_VOLUME_MIN, MASTER_VOLUME_MAX));
    }
    function setTrackVolumeFromY(y) {
        const ratio = 1 - Math.max(0, Math.min((y - TRACK_VOL_TOP) / (TRACK_VOL_BOTTOM - TRACK_VOL_TOP), 1));
        setTrackVolume(sliderRatioToValue(ratio, VOLUME_MIN_PERCENT, VOLUME_MAX_PERCENT));
    }
    const saveTrackVolumes = () => store.set('trackVolume', trackVolumeMap);

    // ===== 曲の一覧 =====
    async function loadPlaylist() {
        const fromJson = await fetchJson('music/tracks.json');
        if (Array.isArray(fromJson)) {
            return fromJson.map(t => typeof t === 'string' ? { src: 'music/' + t } : t)
                .filter(t => t && t.src)
                .map(t => ({ src: t.src, title: t.title || titleFromPath(t.src), art: t.art || null }));
        }
        // tracks.json が無いときは、リポジトリの music/ フォルダの中身をそのまま並べる
        let list = null;
        try { list = JSON.parse(sessionStorage.getItem('thundecky.repoList') || 'null'); } catch (e) { list = null; }
        if (!Array.isArray(list)) {
            const res = await fetchJson(REPO_CONTENTS_API);
            if (Array.isArray(res)) {
                list = res.filter(f => f.type === 'file' && AUDIO_EXT.test(f.name)).map(f => f.path);
                try { sessionStorage.setItem('thundecky.repoList', JSON.stringify(list)); } catch (e) { /* 保存できなくても動く */ }
            }
        }
        if (!Array.isArray(list)) return [];
        return list.sort((a, b) => a.localeCompare(b, 'ja', { numeric: true }))
            .map(p => ({ src: p.split('/').map(encodeURIComponent).join('/'), title: titleFromPath(p), art: null }));
    }
    async function fetchJson(url) {
        try {
            const r = await fetch(url, { cache: 'no-cache' });
            if (!r.ok) return null;
            return await r.json();
        } catch (e) { return null; }
    }
    function titleFromPath(p) {
        let name = decodeURIComponentSafe(p.split('/').pop() || '');
        return name.replace(/\.[^.]+$/, '');
    }
    function decodeURIComponentSafe(s) { try { return decodeURIComponent(s); } catch (e) { return s; } }

    // ===== UI 画像（元アプリの黄色いアイコンを、サイトのオレンジに塗り替える） =====
    const icons = {};
    function loadIcon(name, url) {
        return new Promise(resolve => {
            const img = new Image();
            img.onload = () => { icons[name] = recolor(img); resolve(); };
            img.onerror = () => resolve();
            img.src = url;
        });
    }
    function recolor(img) {
        const c = document.createElement('canvas');
        c.width = img.naturalWidth; c.height = img.naturalHeight;
        const g = c.getContext('2d');
        g.drawImage(img, 0, 0);
        try {
            const d = g.getImageData(0, 0, c.width, c.height);
            const target = rgbToHsl(MAIN);
            for (let i = 0; i < d.data.length; i += 4) {
                if (d.data[i + 3] === 0) continue;
                const [h, s, l] = rgbToHsl([d.data[i], d.data[i + 1], d.data[i + 2]]);
                if (s < 0.35 || h < 30 || h > 70) continue;   // 黄色系だけを置き換える（灰色の OFF アイコンはそのまま）
                const [r, gg, b] = hslToRgb(target[0], Math.min(1, s * target[1] / 0.95), l * (target[2] / 0.5) * 0.98);
                d.data[i] = r; d.data[i + 1] = gg; d.data[i + 2] = b;
            }
            g.putImageData(d, 0, 0);
        } catch (e) { /* 読み取れない場合は元の色のまま */ }
        return c;
    }
    function rgbToHsl([r, g, b]) {
        r /= 255; g /= 255; b /= 255;
        const max = Math.max(r, g, b), min = Math.min(r, g, b), l = (max + min) / 2;
        if (max === min) return [0, 0, l];
        const d = max - min, s = l > 0.5 ? d / (2 - max - min) : d / (max + min);
        let h = max === r ? (g - b) / d + (g < b ? 6 : 0) : max === g ? (b - r) / d + 2 : (r - g) / d + 4;
        return [h * 60, s, l];
    }
    function hslToRgb(h, s, l) {
        l = Math.max(0, Math.min(1, l));
        const k = n => (n + h / 30) % 12, a = s * Math.min(l, 1 - l);
        const f = n => l - a * Math.max(-1, Math.min(k(n) - 3, Math.min(9 - k(n), 1)));
        return [Math.round(f(0) * 255), Math.round(f(8) * 255), Math.round(f(4) * 255)];
    }

    // ===== ジャケット（MP3 に埋め込まれた画像を読む。無ければ NO IMAGE） =====
    const artCache = new Map();     // src -> { canvas, colors, frames: Map }
    const artPending = new Set();
    let placeholderArt = null;

    function getArtData(index) {
        if (!playlist.length) return null;
        const track = playlist[mod(index, playlist.length)];
        const hit = artCache.get(track.src);
        if (hit) return hit;
        if (!artPending.has(track.src)) {
            artPending.add(track.src);
            decodeArt(track).then(entry => {
                artCache.set(track.src, entry || makePlaceholder());
                artPending.delete(track.src);
            });
        }
        return placeholderArt || makePlaceholder();
    }

    function makePlaceholder() {
        if (placeholderArt && icons.noImage) return placeholderArt;
        const c = document.createElement('canvas');
        c.width = c.height = ART_SIZE;
        const g = c.getContext('2d');
        g.fillStyle = rgb(BG); g.fillRect(0, 0, ART_SIZE, ART_SIZE);
        if (icons.noImage) { g.imageSmoothingEnabled = false; g.drawImage(icons.noImage, 0, 0, ART_SIZE, ART_SIZE); }
        const entry = { canvas: c, colors: Array(9).fill(MAIN), frames: new Map() };
        if (icons.noImage) placeholderArt = entry;
        return entry;
    }

    async function decodeArt(track) {
        try {
            let blob = null;
            if (track.art) {
                const r = await fetch(track.art);
                if (r.ok) blob = await r.blob();
            } else if (/\.mp3$/i.test(decodeURIComponentSafe(track.src))) {
                blob = await readId3Picture(track.src);
            }
            if (!blob) return null;
            const img = await blobToImage(blob);
            // 短い辺に合わせて中央を正方形に切り出す（元アプリと同じ）
            const c = document.createElement('canvas');
            c.width = c.height = ART_SIZE;
            const g = c.getContext('2d');
            g.imageSmoothingQuality = 'high';
            const iw = img.naturalWidth || img.width, ih = img.naturalHeight || img.height;
            const s = Math.min(iw, ih);
            g.drawImage(img, (iw - s) / 2, (ih - s) / 2, s, s, 0, 0, ART_SIZE, ART_SIZE);
            return { canvas: c, colors: sampleColors(g), frames: new Map() };
        } catch (e) {
            return null;
        }
    }

    function blobToImage(blob) {
        return new Promise((resolve, reject) => {
            const url = URL.createObjectURL(blob);
            const img = new Image();
            img.onload = () => { URL.revokeObjectURL(url); resolve(img); };
            img.onerror = () => { URL.revokeObjectURL(url); reject(new Error('image')); };
            img.src = url;
        });
    }

    // [左上, 上中, 右上, 右中, 右下, 下中, 左下, 左中] の縁取り用 8 色＋ビジュアライザー用の代表色
    function sampleColors(g) {
        const d = g.getImageData(0, 0, ART_SIZE, ART_SIZE).data;
        const w = ART_SIZE, h = ART_SIZE, cx = w >> 1, cy = h >> 1;
        const pts = [[0, 0], [cx, 0], [w - 1, 0], [w - 1, cy], [w - 1, h - 1], [cx, h - 1], [0, h - 1], [0, cy]];
        const colors = pts.map(([px, py]) => {
            let r = 0, gg = 0, b = 0, n = 0;
            for (let y = Math.max(0, py - 10); y < Math.min(h, py + 10); y++) {
                for (let x = Math.max(0, px - 10); x < Math.min(w, px + 10); x++) {
                    const i = (y * w + x) * 4; r += d[i]; gg += d[i + 1]; b += d[i + 2]; n++;
                }
            }
            return [Math.round(r / n), Math.round(gg / n), Math.round(b / n)];
        });
        colors.push(dominantColor(d));
        return colors;
    }

    function dominantColor(d) {
        // 近い色をまとめて一番多い色を選ぶ。真っ黒・真っ白に近い色は、他に候補があれば除外する
        const buckets = new Map();
        for (let i = 0; i < d.length; i += 4 * 7) {
            if (d[i + 3] < 64) continue;
            const key = (d[i] >> 5) << 6 | (d[i + 1] >> 5) << 3 | (d[i + 2] >> 5);
            const e = buckets.get(key) || { n: 0, r: 0, g: 0, b: 0 };
            e.n++; e.r += d[i]; e.g += d[i + 1]; e.b += d[i + 2];
            buckets.set(key, e);
        }
        const ranked = [...buckets.values()].map(e => {
            const c = [e.r / e.n, e.g / e.n, e.b / e.n];
            return { n: e.n, c, luma: 0.2126 * c[0] + 0.7152 * c[1] + 0.0722 * c[2] };
        });
        if (!ranked.length) return MAIN;
        const visible = ranked.filter(e => e.luma >= 24 && e.luma <= 245);
        const best = (visible.length ? visible : ranked).reduce((a, b) => (b.n > a.n ? b : a));
        let c = best.c;
        if (best.luma < 64) {
            const blend = (64 - best.luma) / Math.max(1, 255 - best.luma);
            c = c.map(v => v + (255 - v) * blend);
        }
        return c.map(v => Math.round(v));
    }

    // ID3v2 の APIC（ジャケット画像）だけを読む。タグの長さぶんだけ Range で取得する
    async function readId3Picture(src) {
        const head = await fetchRange(src, 0, 9);
        if (!head || head.length < 10 || head[0] !== 0x49 || head[1] !== 0x44 || head[2] !== 0x33) return null;
        const ver = head[3];
        const size = syncsafe(head, 6);
        const buf = head.length >= size + 10 ? head : await fetchRange(src, 0, size + 9);
        if (!buf) return null;
        let pos = 10;
        if (head[5] & 0x40) {   // 拡張ヘッダーを飛ばす
            pos += ver === 4 ? syncsafe(buf, 10) : (u32(buf, 10) + 4);
        }
        const end = Math.min(buf.length, size + 10);
        while (pos + 10 <= end) {
            const id = String.fromCharCode(buf[pos], buf[pos + 1], buf[pos + 2], buf[pos + 3]);
            if (!/^[A-Z0-9]{4}$/.test(id)) break;
            const fsize = ver === 4 ? syncsafe(buf, pos + 4) : u32(buf, pos + 4);
            const body = pos + 10;
            if (fsize <= 0 || body + fsize > end) break;
            if (id === 'APIC') {
                const enc = buf[body];
                let p = body + 1;
                let mime = '';
                while (p < body + fsize && buf[p] !== 0) mime += String.fromCharCode(buf[p++]);
                p += 1;             // MIME の終端
                p += 1;             // 画像の種類
                if (enc === 1 || enc === 2) { while (p + 1 < body + fsize && !(buf[p] === 0 && buf[p + 1] === 0)) p += 2; p += 2; }
                else { while (p < body + fsize && buf[p] !== 0) p++; p += 1; }
                if (p >= body + fsize) return null;
                return new Blob([buf.slice(p, body + fsize)], { type: /^image\//.test(mime) ? mime : 'image/jpeg' });
            }
            pos = body + fsize;
        }
        return null;
    }
    async function fetchRange(src, start, endInclusive) {
        try {
            const r = await fetch(src, { headers: { Range: `bytes=${start}-${endInclusive}` } });
            if (!r.ok) return null;
            return new Uint8Array(await r.arrayBuffer());
        } catch (e) { return null; }
    }
    const syncsafe = (b, o) => (b[o] & 0x7f) << 21 | (b[o + 1] & 0x7f) << 14 | (b[o + 2] & 0x7f) << 7 | (b[o + 3] & 0x7f);
    const u32 = (b, o) => ((b[o] << 24) >>> 0) + (b[o + 1] << 16) + (b[o + 2] << 8) + b[o + 3];

    // 3×3 の色を拡大してなめらかな縁取りグラデーションを作る（元アプリの create_gradient_frame）
    function gradientFrame(art, size) {
        let f = art.frames.get(size);
        if (f) return f;
        const [tl, tm, tr, rm, br, bm, bl, lm] = art.colors;
        const all = [tl, tm, tr, rm, br, bm, bl, lm];
        const center = [0, 1, 2].map(k => Math.round(all.reduce((s, c) => s + c[k], 0) / 8));
        const base = document.createElement('canvas');
        base.width = base.height = 3;
        const bg = base.getContext('2d');
        const id = bg.createImageData(3, 3);
        [tl, tm, tr, lm, center, rm, bl, bm, br].forEach((c, i) => { id.data.set([c[0], c[1], c[2], 255], i * 4); });
        bg.putImageData(id, 0, 0);
        f = document.createElement('canvas');
        f.width = f.height = size;
        const fg = f.getContext('2d');
        fg.imageSmoothingEnabled = true;
        fg.imageSmoothingQuality = 'high';
        fg.drawImage(base, 0, 0, size, size);
        art.frames.set(size, f);
        if (art.frames.size > 40) art.frames.delete(art.frames.keys().next().value);
        return f;
    }

    // ===== 背景の幾何学模様（左側の暗い領域だけを右上へ流れる） =====
    class GeometricShape {
        constructor() { this.angle = -Math.PI / 6; this.reset(true); }
        reset(initial) {
            const types = ['filled_square', 'filled_square_small', 'dot_grid', 'single_dot', 'ring'];
            this.type = types[Math.floor(Math.random() * types.length)];
            this.depth = Math.random();
            this.size = Math.floor(24 + this.depth * 82);
            this.alpha = Math.floor(20 + this.depth * 40) / 255;
            this.lineW = this.depth < 0.55 ? 1 : 2;
            const speed = 0.34 + this.depth * 1.05;
            this.vx = speed * Math.cos(this.angle);
            this.vy = speed * Math.sin(this.angle);
            if (initial) {
                this.x = rand(-180, LEFT_W + 180); this.y = rand(-120, H + 120);
            } else if (Math.random() < 0.5) {
                this.x = rand(-120, LEFT_W + 60); this.y = rand(H + 20, H + 160);
            } else {
                this.x = rand(-200, -40); this.y = rand(-60, H + 60);
            }
        }
        update(k) {
            this.x += this.vx * k; this.y += this.vy * k;
            if (this.y < -220 || this.x > LEFT_W + 220) this.reset(false);
        }
        rot(px, py) {
            const c = Math.cos(this.angle), s = Math.sin(this.angle);
            return [this.x + px * c - py * s, this.y + px * s + py * c];
        }
        poly(half) {
            ctx.beginPath();
            [[-half, -half], [half, -half], [half, half], [-half, half]].forEach(([px, py], i) => {
                const [x, y] = this.rot(px, py); i ? ctx.lineTo(x, y) : ctx.moveTo(x, y);
            });
            ctx.closePath(); ctx.fill();
        }
        draw() {
            const m = this.size + 28;
            if (this.x < -m || this.y < -m || this.x > LEFT_W + m || this.y > H + m) return;
            ctx.fillStyle = ctx.strokeStyle = rgb(MAIN, this.alpha);
            const half = this.size / 2;
            if (this.type === 'filled_square') this.poly(half);
            else if (this.type === 'filled_square_small') this.poly(half * 0.62);
            else if (this.type === 'ring') {
                ctx.lineWidth = this.lineW; ctx.beginPath();
                ctx.arc(this.x, this.y, Math.max(5, Math.floor(half * 0.72)), 0, Math.PI * 2); ctx.stroke();
            } else if (this.type === 'single_dot') {
                ctx.beginPath(); ctx.arc(this.x, this.y, Math.max(1, Math.floor(half * 0.18)), 0, Math.PI * 2); ctx.fill();
            } else {
                const spacing = Math.max(10, Math.floor(this.size * 0.16)), r = Math.max(1, Math.floor(this.size * 0.035));
                const x0 = -spacing * 2, y0 = -spacing * 3;
                for (let gy = 0; gy < 7; gy++) for (let gx = 0; gx < 5; gx++) {
                    if (this.depth < 0.65 && ((gx === 0 && gy === 0) || (gx === 4 && gy === 6) || (gx === 0 && gy === 6))) continue;
                    const [x, y] = this.rot(x0 + gx * spacing, y0 + gy * spacing);
                    ctx.beginPath(); ctx.arc(x, y, r, 0, Math.PI * 2); ctx.fill();
                }
            }
        }
    }
    const shapes = Array.from({ length: 24 }, () => new GeometricShape());

    // ===== 描画の部品 =====
    function textWithShadow(text, font, color, x, y) {
        ctx.font = font;
        ctx.textBaseline = 'top';
        ctx.fillStyle = rgb(SHADOW); ctx.fillText(text, x + SHADOW_OFFSET, y + SHADOW_OFFSET);
        ctx.fillStyle = rgb(color); ctx.fillText(text, x, y);
        return ctx.measureText(text).width;
    }
    function chamferPath(x, y, w, h, cut) {
        const c = Math.max(2, Math.min(cut, Math.floor(w / 4), Math.floor(h / 4))), r = x + w, b = y + h;
        ctx.beginPath();
        ctx.moveTo(x + c, y); ctx.lineTo(r - c, y); ctx.lineTo(r, y + c); ctx.lineTo(r, b - c);
        ctx.lineTo(r - c, b); ctx.lineTo(x + c, b); ctx.lineTo(x, b - c); ctx.lineTo(x, y + c);
        ctx.closePath();
    }
    function techPanel(x, y, w, h, { fill = PANEL_FILL, cut = 10, shadow = true, inner = true } = {}) {
        if (shadow) { ctx.save(); ctx.translate(SHADOW_OFFSET, SHADOW_OFFSET); chamferPath(x, y, w, h, cut); ctx.fillStyle = rgb(SHADOW); ctx.fill(); ctx.restore(); }
        chamferPath(x, y, w, h, cut);
        ctx.fillStyle = rgb(fill); ctx.fill();
        ctx.lineWidth = 2; ctx.strokeStyle = rgb(MAIN); ctx.stroke();
        if (inner && w > 40 && h > 24) {
            chamferPath(x + 5, y + 5, w - 10, h - 10, Math.max(4, cut - 4));
            ctx.lineWidth = 1; ctx.strokeStyle = rgb(SUB_LINE); ctx.stroke();
        }
    }
    function knob(cx, cy, body, lines) {
        roundRect(cx - 14, cy - 12, 28, 24, 3); ctx.fillStyle = rgb(body); ctx.fill();
        ctx.strokeStyle = rgb(lines); ctx.lineWidth = 2;
        for (let n = 0; n < 3; n++) { const ly = cy - 12 + 7 + n * 5; line(cx - 8, ly, cx + 8, ly); }
    }
    function roundRect(x, y, w, h, r) {
        ctx.beginPath();
        ctx.moveTo(x + r, y); ctx.arcTo(x + w, y, x + w, y + h, r); ctx.arcTo(x + w, y + h, x, y + h, r);
        ctx.arcTo(x, y + h, x, y, r); ctx.arcTo(x, y, x + w, y, r); ctx.closePath();
    }
    function line(x1, y1, x2, y2) { ctx.beginPath(); ctx.moveTo(x1, y1); ctx.lineTo(x2, y2); ctx.stroke(); }
    const inRect = (r, x, y) => r && x >= r[0] && x < r[0] + r[2] && y >= r[1] && y < r[1] + r[3];

    function drawPreviewSlot(x, y, w, h, index) {
        techPanel(x, y, w, h, { cut: 10, shadow: false, inner: false });
        if (!playlist.length) return;
        const pad = 7, size = Math.min(w, h) - pad * 2;
        const art = getArtData(index);
        const ax = x + w / 2 - size / 2, ay = y + h / 2 - size / 2;
        ctx.drawImage(art.canvas, ax, ay, size, size);
        ctx.lineWidth = 1; ctx.strokeStyle = rgb(MAIN); ctx.strokeRect(ax - 1.5, ay - 1.5, size + 3, size + 3);
    }

    function drawRightPanel(now) {
        ctx.fillStyle = rgb(MAIN); ctx.fillRect(PANEL_X, 0, W - PANEL_X, H);
        const cx = PANEL_X + (W - PANEL_X) / 2;
        ctx.fillStyle = rgb(BG); ctx.textBaseline = 'top'; ctx.textAlign = 'center';
        ctx.font = `72px ${FONT_UI}`;
        ctx.fillText(pad2(now.getHours()), cx, 30);
        ctx.fillText(pad2(now.getMinutes()), cx, 118);
        ctx.strokeStyle = rgb(BG); ctx.lineWidth = 2; line(PANEL_X + 14, 210, W - 14, 210);
        ctx.textAlign = 'left'; ctx.font = `22px ${FONT_UI}`;
        ctx.fillText(String(now.getFullYear()), PANEL_X + 14, 222);
        ctx.fillText(`${pad2(now.getMonth() + 1)}/${pad2(now.getDate())}`, PANEL_X + 14, 248);
        ctx.fillText(['Sun', 'Mon', 'Tue', 'Wed', 'Thu', 'Fri', 'Sat'][now.getDay()], PANEL_X + 14, 274);

        const volCx = W - 30;
        ctx.textAlign = 'center'; ctx.fillText('VOL', volCx, 372); ctx.textAlign = 'left';
        ctx.lineWidth = 5; line(volCx, MASTER_VOL_TOP, volCx, MASTER_VOL_BOTTOM);
        const knobY = MASTER_VOL_TOP + (MASTER_VOL_BOTTOM - MASTER_VOL_TOP) * (1 - valueToSliderRatio(masterValue, MASTER_VOLUME_MIN, MASTER_VOLUME_MAX));
        knob(volCx, Math.round(knobY), BG, MAIN);
        volRect = [volCx - 18, MASTER_VOL_TOP - 12, 36, MASTER_VOL_BOTTOM - MASTER_VOL_TOP + 24];
    }

    function drawVisualizer(dtK) {
        if (!currentArtRect || !playlist.length) return;
        const target = new Float32Array(VIS_NUM_BARS);
        if (isPlaying && !audio.paused && analyser) {
            analyser.getFloatFrequencyData(freqData);
            const binHz = audioCtx.sampleRate / analyser.fftSize;
            const lo = Math.log10(50), hi = Math.log10(11025);
            const raw = new Float32Array(VIS_NUM_BARS);
            for (let b = 0; b < VIS_NUM_BARS; b++) {
                const f0 = Math.pow(10, lo + (hi - lo) * b / VIS_NUM_BARS), f1 = Math.pow(10, lo + (hi - lo) * (b + 1) / VIS_NUM_BARS);
                let i0 = Math.max(1, Math.floor(f0 / binHz)), i1 = Math.max(i0 + 1, Math.ceil(f1 / binHz));
                let s = 0, n = 0;
                for (let i = i0; i < i1 && i < freqData.length; i++) { s += Math.pow(10, freqData[i] / 20); n++; }
                raw[b] = Math.log1p((n ? s / n : 0) * 60);
            }
            // 帯域ごとの最近のピークで割って、低音だけが長くならないようにそろえる（元アプリの balance_visualizer_spectrum の近似）
            let globalPeak = 1e-6;
            for (let b = 0; b < VIS_NUM_BARS; b++) {
                bandPeaks[b] = Math.max(bandPeaks[b] * 0.9985, raw[b]);
                globalPeak = Math.max(globalPeak, bandPeaks[b]);
            }
            for (let b = 0; b < VIS_NUM_BARS; b++) {
                const bp = Math.max(bandPeaks[b], globalPeak * 0.06);
                const v = Math.min(1, raw[b] / bp * 0.82 + raw[b] / globalPeak * 0.18);
                target[b] = Math.pow(Math.max(0, v), 0.78);
            }
        }
        const scale = Math.max(0, Math.min(1, (masterValue / MASTER_VOLUME_MAX) * getTrackVolume()));
        let maxLevel = 0;
        for (let b = 0; b < VIS_NUM_BARS; b++) {
            const t = target[b] * scale;
            const coeff = 1 - Math.pow(1 - (t > visLevels[b] ? VIS_ATTACK : VIS_DECAY), dtK);
            visLevels[b] += (t - visLevels[b]) * coeff;
            maxLevel = Math.max(maxLevel, visLevels[b]);
        }
        if (maxLevel < 0.01) return;
        const color = (getArtData(currentIndex).colors[8]) || MAIN;
        const [rx, ry, rw, rh] = currentArtRect;
        const leftX = rx - VIS_GAP_FROM_ART, rightX = rx + rw + VIS_GAP_FROM_ART;
        for (let b = 0; b < VIS_NUM_BARS; b++) {
            const y0 = Math.round(ry + b * rh / VIS_NUM_BARS), y1 = Math.round(ry + (b + 1) * rh / VIS_NUM_BARS);
            const h = Math.max(1, y1 - y0), len = Math.floor(visLevels[b] * VIS_MAX_LEN);
            if (len < 1) continue;
            ctx.fillStyle = rgb(SHADOW);
            ctx.fillRect(leftX - len + SHADOW_OFFSET, y0 + SHADOW_OFFSET, len, h);
            ctx.fillRect(rightX + SHADOW_OFFSET, y0 + SHADOW_OFFSET, len, h);
            ctx.fillStyle = rgb(color);
            ctx.fillRect(leftX - len, y0, len, h);
            ctx.fillRect(rightX, y0, len, h);
        }
    }

    function drawTrackVolumeControl() {
        if (!playlist.length) { trackVolRect = null; return; }
        const x = TRACK_VOL_X, trackH = TRACK_VOL_BOTTOM - TRACK_VOL_TOP;
        const knobY = Math.round(TRACK_VOL_TOP + trackH * (1 - valueToSliderRatio(getTrackVolumePercent(), VOLUME_MIN_PERCENT, VOLUME_MAX_PERCENT)));
        ctx.lineWidth = 5;
        ctx.strokeStyle = rgb(SHADOW); line(x + SHADOW_OFFSET, TRACK_VOL_TOP + SHADOW_OFFSET, x + SHADOW_OFFSET, TRACK_VOL_BOTTOM + SHADOW_OFFSET);
        ctx.strokeStyle = rgb(MAIN); line(x, TRACK_VOL_TOP, x, TRACK_VOL_BOTTOM);
        roundRect(x - 14 + SHADOW_OFFSET, knobY - 12 + SHADOW_OFFSET, 28, 24, 3); ctx.fillStyle = rgb(SHADOW); ctx.fill();
        knob(x, knobY, MAIN, BG);
        trackVolRect = [x - 20, TRACK_VOL_TOP - 16, 40, trackH + 32];
    }

    function drawPlayer(dt) {
        const dtK = Math.min(4, dt * 60);
        ctx.fillStyle = rgb(BG); ctx.fillRect(0, 0, W, H);

        // 背景の幾何学模様（左の暗い領域だけ）
        ctx.save(); ctx.beginPath(); ctx.rect(0, 0, LEFT_W, H); ctx.clip();
        [...shapes].sort((a, b) => a.depth - b.depth).forEach(s => s.draw());
        ctx.restore();

        drawRightPanel(new Date());

        if (!playlist.length) {
            playRect = seekRect = loopRect = trackVolRect = topSlotRect = bottomSlotRect = currentArtRect = null;
            ctx.textAlign = 'center';
            textWithShadow(loaded ? 'NO MUSIC' : 'LOADING...', `22px ${FONT_UI}`, MAIN, LEFT_W / 2, H / 2 - 11);
            ctx.textAlign = 'left';
            drawBorder();
            return;
        }

        // 曲番号（元アプリのフォルダボタンの位置）
        textWithShadow(`${pad2(mod(currentIndex, playlist.length) + 1)}/${pad2(playlist.length)}`, `22px ${FONT_UI}`, MAIN, 22, 28);

        const baseIdx = currentIndex;
        topSlotRect = [177, 7, 106, 106];
        bottomSlotRect = [177, 487, 106, 106];
        drawPreviewSlot(...topSlotRect, baseIdx + 1);
        drawPreviewSlot(...bottomSlotRect, baseIdx - 1);

        // 縦カルーセル
        const [centerX, centerY] = ART_CENTER;
        ctx.save(); ctx.beginPath(); ctx.rect(75, 3, 320, 592); ctx.clip();
        const centerI = Math.round(visualOffset);
        const range = [centerI - 2, centerI - 1, centerI, centerI + 1, centerI + 2].sort((a, b) => Math.abs(b - visualOffset) - Math.abs(a - visualOffset));
        currentArtRect = null;
        for (const i of range) {
            const pos = i - visualOffset, dist = Math.abs(pos);
            if (dist > 2.5) continue;
            const scale = 1 - Math.min(dist, 1) * 0.28;
            const x = centerX, y = centerY - pos * V_SPACING;
            const size = Math.floor(ART_SIZE * scale);
            if (size < 10) continue;
            const art = getArtData(baseIdx + i);
            const fGap = Math.floor(FRAME_GAP * scale), fW = Math.floor(FRAME_WIDTH * scale);
            const frameSize = size + (fGap + fW) * 2;
            const grad = gradientFrame(art, frameSize);
            const rx = x - Math.floor(frameSize / 2), ry = Math.floor(y - frameSize / 2);
            const innerSize = size + fGap * 2;
            const paint = () => {
                ctx.drawImage(grad, rx, ry);
                ctx.fillStyle = rgb(BG); ctx.fillRect(x - Math.floor(innerSize / 2), Math.floor(y - innerSize / 2), innerSize, innerSize);
                ctx.drawImage(art.canvas, x - Math.floor(size / 2), Math.floor(y - size / 2), size, size);
            };
            ctx.fillStyle = rgb(SHADOW); ctx.fillRect(rx + SHADOW_OFFSET, ry + SHADOW_OFFSET, frameSize, frameSize);
            paint();
            if (i === 0 && !isAnimating) {
                techPanel(x - size / 2 - 10, Math.floor(y - size / 2 - 10), size + 20, size + 20, { fill: [10, 10, 10], cut: 10, shadow: false, inner: false });
                paint();
                currentArtRect = [x - Math.floor(size / 2), Math.floor(y - size / 2), size, size];
            }
        }
        ctx.restore();

        drawVisualizer(dtK);
        drawTrackVolumeControl();

        // 再生位置
        let progress = 0, curSec = 0;
        const total = isFinite(audio.duration) ? audio.duration : 0;
        const sameTrack = audio.src && currentTrack() && audio.src === new URL(currentTrack().src, location.href).href;
        if (seeking) { progress = seekDragRatio; curSec = total * progress; }
        else if (sameTrack && total > 0 && (isPlaying || isPaused)) { curSec = audio.currentTime; progress = Math.min(curSec / total, 1); }
        const timeStr = `${Math.floor(curSec / 60)}:${pad2(Math.floor(curSec % 60))}`;

        // タイトル＋再生バーのパネル
        const px = 78, py = 403, pw = 350, ph = 96;
        techPanel(px, py, pw, ph, { cut: 12, shadow: true, inner: true });
        const title = currentTrack().title || '';
        if (title !== lastTitle) { lastTitle = title; titleScrollX = 0; }
        const ta = [px + 18, py + 10, pw - 36, 24];
        ctx.save(); ctx.beginPath(); ctx.rect(...ta); ctx.clip();
        ctx.font = `22px ${FONT_TITLE}`;
        const tw = ctx.measureText(title).width;
        let textX;
        if (tw > ta[2]) {
            titleScrollX -= 0.5 * dtK;
            if (titleScrollX < -tw) titleScrollX = ta[2];
            textX = Math.round(titleScrollX) + ta[0];
        } else {
            textX = ta[0] + ta[2] / 2 - tw / 2;
        }
        textWithShadow(title, `22px ${FONT_TITLE}`, MAIN, textX, ta[1] + 1);
        ctx.restore();
        ctx.strokeStyle = rgb(SUB_LINE); ctx.lineWidth = 1; line(px + 16, py + 40.5, px + pw - 16, py + 40.5);

        // 再生／一時停止
        const ctrlY = py + 70, bx = px + 28;
        const drawPlayShape = (ox, oy, col) => {
            ctx.fillStyle = rgb(col);
            if (isPlaying) {
                ctx.fillRect(bx - 5 - 3 + ox, ctrlY - 10 + oy, 6, 20);
                ctx.fillRect(bx + 5 - 3 + ox, ctrlY - 10 + oy, 6, 20);
            } else {
                ctx.beginPath(); ctx.moveTo(bx - 8 + ox, ctrlY - 12 + oy); ctx.lineTo(bx + 12 + ox, ctrlY + oy); ctx.lineTo(bx - 8 + ox, ctrlY + 12 + oy); ctx.closePath(); ctx.fill();
            }
        };
        drawPlayShape(SHADOW_OFFSET, SHADOW_OFFSET, SHADOW);
        drawPlayShape(0, 0, MAIN);
        playRect = [bx - 15, ctrlY - 15, 30, 30];

        // シークバー
        const barX = px + 58, barW = 210;
        ctx.lineWidth = 4;
        ctx.strokeStyle = rgb(SHADOW); line(barX + SHADOW_OFFSET, ctrlY + SHADOW_OFFSET, barX + barW + SHADOW_OFFSET, ctrlY + SHADOW_OFFSET);
        ctx.strokeStyle = rgb(SEEK_TRACK); line(barX, ctrlY, barX + barW, ctrlY);
        ctx.strokeStyle = rgb(MAIN); if (progress > 0) line(barX, ctrlY, barX + barW * progress, ctrlY);
        ctx.fillStyle = rgb(MAIN); ctx.beginPath(); ctx.arc(barX + barW * progress, ctrlY, 7, 0, Math.PI * 2); ctx.fill();
        seekRect = [barX, ctrlY - 10, barW, 20];
        textWithShadow(timeStr, `16px ${FONT_UI}`, MAIN, barX + barW + 12, ctrlY - 8);

        // 1 曲ループ
        const loopImg = loopOne ? icons.loopOn : icons.loopOff;
        if (loopImg) { ctx.imageSmoothingEnabled = false; ctx.drawImage(loopImg, 44 - 20, 566 - 20, 40, 40); ctx.imageSmoothingEnabled = true; }
        loopRect = [22, 544, 44, 44];

        drawBorder();
    }

    function drawBorder() {
        ctx.lineWidth = BORDER_WIDTH; ctx.strokeStyle = rgb(MAIN);
        ctx.strokeRect(BORDER_WIDTH / 2, BORDER_WIDTH / 2, W - BORDER_WIDTH, H - BORDER_WIDTH);
    }

    // ===== 曲送りアニメーション =====
    function beginOffsetAnim(target, step, playAfter, duration) {
        animStart = visualOffset; animTarget = target; animTimer = 0;
        animDuration = REDUCE_MOTION ? 0.01 : (duration || ANIM_DURATION);
        isAnimating = true;
        if (playAfter === undefined) playAfter = step !== 0 && isPlaying && !isPaused;
        if (step !== 0) { moveDirection = step; stopAudioPlayback(); } else moveDirection = 0;
        playAfterAnimation = !!playAfter;
    }
    function triggerAnimation(d) { if (isAnimating) return; beginOffsetAnim(d, d); }
    function canPerformAction() {
        const t = performance.now() / 1000;
        if (t - lastActionTime > ACTION_COOLDOWN) { lastActionTime = t; return true; }
        return false;
    }
    function finishAnimation() {
        const step = moveDirection, playAfter = playAfterAnimation;
        if (step !== 0 && playlist.length) {
            currentIndex = mod(currentIndex + step, playlist.length);
            audio.removeAttribute('src'); audio.load();
            applyEffectiveVolume();
        }
        isAnimating = false; visualOffset = 0; moveDirection = 0; animStart = animTarget = 0; playAfterAnimation = false;
        if (playAfter && playlist.length) startAudio(currentIndex);
    }

    function update(dt) {
        const k = REDUCE_MOTION ? 0 : Math.min(4, dt * 60);
        shapes.forEach(s => s.update(k));
        if (isAnimating) {
            animTimer += dt;
            const p = Math.min(animTimer / Math.max(animDuration, 1e-6), 1);
            const eased = 1 - Math.pow(1 - p, 4);
            visualOffset = animStart + (animTarget - animStart) * eased;
            if (p >= 1) finishAnimation();
        }
        if (playlist.length) for (const off of [-2, -1, 0, 1, 2]) getArtData(currentIndex + (isAnimating ? moveDirection : 0) + off);
    }

    // ===== 入力 =====
    function toLocal(e) {
        const r = canvas.getBoundingClientRect();
        return [(e.clientX - r.left) / r.width * W, (e.clientY - r.top) / r.height * H];
    }
    let activePointer = null;
    canvas.addEventListener('pointerdown', e => {
        if (e.button !== 0) return;
        const [x, y] = toLocal(e);
        canvas.focus({ preventScroll: true });
        let captured = true;
        if (inRect(playRect, x, y)) togglePlay();
        else if (inRect(loopRect, x, y)) { loopOne = !loopOne; store.set('loopOne', loopOne); }
        else if (inRect(trackVolRect, x, y)) { trackVolumeDragging = true; setTrackVolumeFromY(y); }
        else if (inRect(volRect, x, y)) { masterDragging = true; setMasterFromY(y); }
        else if (inRect(seekRect, x, y) && playlist.length) { seeking = true; seekDragRatio = clamp01((x - seekRect[0]) / seekRect[2]); }
        else if (inRect(topSlotRect, x, y) && playlist.length) { if (!isAnimating && canPerformAction()) triggerAnimation(1); captured = false; }
        else if (inRect(bottomSlotRect, x, y) && playlist.length) { if (!isAnimating && canPerformAction()) triggerAnimation(-1); captured = false; }
        else if (x < PANEL_X && playlist.length && e.pointerType === 'mouse') { swiping = true; swipeStart = [x, y]; swipeMoved = false; resumeAfterScroll = false; }
        else captured = false;
        if (captured) { activePointer = e.pointerId; try { canvas.setPointerCapture(e.pointerId); } catch (err) { /* 無くても動く */ } e.preventDefault(); }
    });
    canvas.addEventListener('pointermove', e => {
        const [x, y] = toLocal(e);
        canvas.style.cursor = (inRect(playRect, x, y) || inRect(loopRect, x, y) || inRect(seekRect, x, y) || inRect(trackVolRect, x, y) || inRect(volRect, x, y) || inRect(topSlotRect, x, y) || inRect(bottomSlotRect, x, y)) ? 'pointer' : (swiping ? 'grabbing' : 'default');
        if (e.pointerId !== activePointer) return;
        if (trackVolumeDragging) setTrackVolumeFromY(y);
        else if (masterDragging) setMasterFromY(y);
        else if (seeking) seekDragRatio = clamp01((x - seekRect[0]) / seekRect[2]);
        else if (swiping && !isAnimating) {
            const dy = y - swipeStart[1];
            if (Math.abs(dy) > CLICK_MOVE_TOLERANCE && !swipeMoved) {
                swipeMoved = true;
                resumeAfterScroll = isPlaying && !isPaused;
                stopAudioPlayback();
            }
            if (swipeMoved) visualOffset = Math.max(-2.4, Math.min(2.4, dy / SWIPE_SPACING));
        }
    });
    const endPointer = e => {
        if (e.pointerId !== activePointer) return;
        activePointer = null;
        if (trackVolumeDragging) { trackVolumeDragging = false; saveTrackVolumes(); }
        else if (masterDragging) masterDragging = false;
        else if (seeking) {
            seeking = false;
            const total = isFinite(audio.duration) ? audio.duration : 0;
            const sameTrack = audio.src === new URL(currentTrack().src, location.href).href;
            if (sameTrack && total > 0) {
                audio.currentTime = total * seekDragRatio;
                if (!isPlaying) togglePlay();
            } else {
                startAudio(currentIndex, 0);
                audio.addEventListener('loadedmetadata', () => { audio.currentTime = audio.duration * seekDragRatio; }, { once: true });
            }
        } else if (swiping) {
            swiping = false;
            if (swipeMoved && !isAnimating) {
                const off = visualOffset;
                let step = 0;
                if (Math.abs(off) >= SWIPE_THRESHOLD) { step = Math.round(off) || (off > 0 ? 1 : -1); }
                const playAfter = resumeAfterScroll; resumeAfterScroll = false;
                beginOffsetAnim(step, step, playAfter);
                if (step === 0 && playAfter) playAfterAnimation = false, startAudio(currentIndex, audio.currentTime);
            }
        }
    };
    canvas.addEventListener('pointerup', endPointer);
    canvas.addEventListener('pointercancel', endPointer);

    // ホイール：音量バーの上なら微調整、ジャケットの列なら曲送り。それ以外はページのスクロールをじゃましない
    canvas.addEventListener('wheel', e => {
        if (!e.deltaY) return;
        const [x, y] = toLocal(e);
        const up = e.deltaY < 0;
        if (inRect(trackVolRect, x, y) && playlist.length) {
            setTrackVolume(getTrackVolumePercent() + (up ? TRACK_VOLUME_WHEEL_STEP : -TRACK_VOLUME_WHEEL_STEP)); saveTrackVolumes();
        } else if (inRect(volRect, x, y)) {
            setMaster(masterValue + (up ? MASTER_VOLUME_WHEEL_STEP : -MASTER_VOLUME_WHEEL_STEP));
        } else if (x >= 75 && x < 395 && playlist.length && !seeking && !swiping) {
            const d = up ? 1 : -1;
            if (isAnimating) { animStart = visualOffset; animTarget += d; moveDirection += d; animTimer = 0; animDuration = WHEEL_ANIM_DURATION; }
            else beginOffsetAnim(d, d, undefined, WHEEL_ANIM_DURATION);
        } else return;
        e.preventDefault();
    }, { passive: false });

    // キーボード（プレイヤーをクリック・Tab で選んでいるときだけ）
    canvas.addEventListener('keydown', e => {
        if (e.key === ' ' || e.key === 'Spacebar') togglePlay();
        else if (e.key === 'ArrowUp') { if (playlist.length && !isAnimating && (e.repeat || canPerformAction())) triggerAnimation(1); }
        else if (e.key === 'ArrowDown') { if (playlist.length && !isAnimating && (e.repeat || canPerformAction())) triggerAnimation(-1); }
        else if (e.key === 'ArrowRight') setMaster(masterValue + MASTER_VOLUME_STEP);
        else if (e.key === 'ArrowLeft') setMaster(masterValue - MASTER_VOLUME_STEP);
        else return;
        e.preventDefault();
    });

    // ===== ループ（画面外・最小化中・タブ非表示のときは描かない） =====
    let visible = true, rafId = 0, lastT = 0;
    const win = canvas.closest('.window');
    function isShown() { return visible && !(win && win.classList.contains('collapsed')) && !document.hidden; }
    function frame(t) {
        rafId = 0;
        const dt = lastT ? Math.min(0.1, (t - lastT) / 1000) : 1 / 60;
        lastT = t;
        update(dt);
        drawPlayer(dt);
        if (isShown()) rafId = requestAnimationFrame(frame);
        else lastT = 0;
    }
    function kick() { if (!rafId && isShown()) rafId = requestAnimationFrame(frame); }
    if ('IntersectionObserver' in window) {
        new IntersectionObserver(es => { visible = es[0].isIntersecting; kick(); }, { rootMargin: '100px' }).observe(canvas);
    }
    document.addEventListener('visibilitychange', kick);
    if (win) new MutationObserver(kick).observe(win, { attributes: true, attributeFilter: ['class'] });

    function resize() {
        const dpr = Math.min(2, window.devicePixelRatio || 1);
        const cssW = canvas.getBoundingClientRect().width || W;
        const px = Math.round(Math.max(W, cssW * dpr));
        if (canvas.width !== px) { canvas.width = canvas.height = px; }
        ctx.setTransform(px / W, 0, 0, px / H, 0, 0);
        ctx.imageSmoothingEnabled = true;
        kick();
    }
    window.addEventListener('resize', resize);

    // ===== 起動 =====
    const mod = (n, m) => ((n % m) + m) % m;
    const pad2 = n => String(n).padStart(2, '0');
    const clamp01 = v => Math.max(0, Math.min(1, v));
    function rand(a, b) { return a + Math.random() * (b - a); }

    resize();
    Promise.all([
        loadIcon('loopOn', 'images/thundecky/RoopUI_On.png'),
        loadIcon('loopOff', 'images/thundecky/RoopUI_Off.png'),
        loadIcon('noImage', 'images/thundecky/NoImage.png'),
        document.fonts ? document.fonts.load(`22px ${FONT_UI}`).catch(() => {}) : null
    ]).then(async () => {
        makePlaceholder();
        playlist = await loadPlaylist();
        loaded = true;
        currentIndex = 0;
        if (document.fonts) document.fonts.load(`22px ${FONT_TITLE}`, playlist.map(t => t.title).join('')).catch(() => {});
        kick();
    });
})();
