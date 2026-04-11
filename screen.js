// Piano Highway plugin — Synthesia-style scrolling piano renderer
// with MIDI keyboard input, WebAudioFont synthesizer, and accuracy scoring.
// Activates when a "Keys" or "Piano" arrangement is loaded, or via toggle button.

(function () {
'use strict';

// ═══════════════════════════════════════════════════════════════════════
// State
// ═══════════════════════════════════════════════════════════════════════

let _pianoEnabled = false;
let _pianoAuto = false;
let _pianoCanvas = null;
let _pianoCtx = null;
let _rafId = null;
let _settingsPanel = null;
let _settingsVisible = false;

// ── Persisted settings ───────────────────────────────────────────────

const _cfg = {
    midiInputId:   localStorage.getItem('piano_midi_input') || '',
    instrumentIdx: parseInt(localStorage.getItem('piano_instrument') || '0'),
    synthVolume:   parseFloat(localStorage.getItem('piano_synth_vol') || '0.7'),
    midiChannel:   parseInt(localStorage.getItem('piano_midi_ch') || '-1'),
    transpose:     parseInt(localStorage.getItem('piano_transpose') || '0'),
    showNoteNames: localStorage.getItem('piano_note_names') !== 'false',
    hitDetection:  localStorage.getItem('piano_hit_detect') === 'true',
};

function _saveCfg(key, val) {
    _cfg[key] = val;
    const storeKey = 'piano_' + key.replace(/[A-Z]/g, c => '_' + c.toLowerCase());
    localStorage.setItem(storeKey, String(val));
}

// ── MIDI input state ─────────────────────────────────────────────────

let _midiAccess = null;
let _midiInput = null;
const _heldNotes = new Map();      // transposed midi -> velocity
let _sustainOn = false;
const _sustainedNotes = new Set();  // midi notes pending release on pedal up

// ── Synth state ──────────────────────────────────────────────────────

let _audioCtx = null;
let _synthPlayer = null;
let _synthPreset = null;
let _synthGain = null;
const _noteEnvelopes = new Map();   // transposed midi -> envelope from queueWaveTable
let _synthLoading = false;
let _playerScriptLoaded = false;

// ── Hit detection state ──────────────────────────────────────────────

const HIT_TOLERANCE = 0.10;        // seconds
let _hits = 0, _misses = 0, _streak = 0, _bestStreak = 0;
const _hitNoteKeys = new Set();     // "time|midi" strings for correctly hit notes
const _wrongFlashes = [];           // [{midi, wall}] for brief red flashes
const _missedNoteKeys = new Set();  // "time|midi" strings for notes that passed unplayed

// ═══════════════════════════════════════════════════════════════════════
// MIDI Helpers
// ═══════════════════════════════════════════════════════════════════════

const NOTE_NAMES = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B'];

function noteToMidi(string, fret) { return string * 24 + fret; }

function midiToNoteName(midi) {
    return NOTE_NAMES[midi % 12] + (Math.floor(midi / 12) - 1);
}

function isBlackKey(midi) {
    const pc = midi % 12;
    return pc === 1 || pc === 3 || pc === 6 || pc === 8 || pc === 10;
}

function _noteKey(time, midi) {
    return time.toFixed(3) + '|' + midi;
}

// ═══════════════════════════════════════════════════════════════════════
// Color Palette
// ═══════════════════════════════════════════════════════════════════════

const OCTAVE_COLORS = [
    '#ff4466', '#ff8844', '#ffcc33', '#66dd55', '#44ccaa',
    '#44aaff', '#7766ff', '#cc55ff', '#ff55aa', '#aaaaaa',
];
const OCTAVE_DIM = [
    '#992233', '#994422', '#997711', '#338822', '#227755',
    '#225588', '#443399', '#772299', '#992255', '#555555',
];

// Feedback colors
const COL_SONG_ACTIVE  = '#22cc66';  // song note at now line
const COL_PLAYER       = '#4488ff';  // player pressed, no match
const COL_HIT          = '#00ff44';  // correct hit
const COL_WRONG        = '#ff4444';  // wrong note flash
const COL_MISSED       = '#555566';  // missed note

function noteColor(midi, bright) {
    const octave = Math.floor(midi / 12);
    const palette = bright ? OCTAVE_COLORS : OCTAVE_DIM;
    return palette[Math.min(octave, palette.length - 1)];
}

// ═══════════════════════════════════════════════════════════════════════
// Configuration
// ═══════════════════════════════════════════════════════════════════════

const VISIBLE_SECONDS = 3.0;
const NOW_LINE_Y_FRAC = 0.82;
const KEYBOARD_H_FRAC = 0.15;
const NOTE_LABEL_MIN_H = 16;

// ═══════════════════════════════════════════════════════════════════════
// Instruments (WebAudioFont — General MIDI via JCLive soundfont)
// ═══════════════════════════════════════════════════════════════════════

const WAF_BASE = 'https://surikov.github.io/webaudiofontdata/sound/';
const WAF_PLAYER_URL = 'https://surikov.github.io/webaudiofont/npm/dist/WebAudioFontPlayer.js';
const WAF_SF = 'JCLive_sf2_file';

const INSTRUMENTS = [
    { name: 'Grand Piano',    gm: 0  },
    { name: 'Electric Piano',  gm: 4  },
    { name: 'Honky-tonk',      gm: 3  },
    { name: 'Organ',            gm: 19 },
    { name: 'Strings',          gm: 48 },
    { name: 'Synth Lead',       gm: 80 },
    { name: 'Synth Pad',        gm: 88 },
    { name: 'Harpsichord',      gm: 6  },
    { name: 'Vibraphone',       gm: 11 },
    { name: 'Music Box',        gm: 10 },
];

function _wafFile(gm) {
    return String(gm * 10).padStart(4, '0') + '_' + WAF_SF;
}

function _wafVar(gm)  { return '_tone_' + _wafFile(gm); }
function _wafUrl(gm)  { return WAF_BASE + _wafFile(gm) + '.js'; }

// ═══════════════════════════════════════════════════════════════════════
// Script Loader
// ═══════════════════════════════════════════════════════════════════════

function _loadScript(url) {
    return new Promise((resolve, reject) => {
        if (document.querySelector(`script[src="${url}"]`)) { resolve(); return; }
        const s = document.createElement('script');
        s.src = url;
        s.onload = resolve;
        s.onerror = () => reject(new Error('Failed to load ' + url));
        document.head.appendChild(s);
    });
}

// ═══════════════════════════════════════════════════════════════════════
// WebAudioFont Synthesizer
// ═══════════════════════════════════════════════════════════════════════

async function _synthInit() {
    if (_synthPlayer) return;
    try {
        if (!_playerScriptLoaded) {
            await _loadScript(WAF_PLAYER_URL);
            _playerScriptLoaded = true;
        }
        if (typeof WebAudioFontPlayer === 'undefined') return;

        _audioCtx = new (window.AudioContext || window.webkitAudioContext)();
        _synthGain = _audioCtx.createGain();
        _synthGain.gain.value = _cfg.synthVolume;
        _synthGain.connect(_audioCtx.destination);
        _synthPlayer = new WebAudioFontPlayer();

        await _synthLoadInstrument(_cfg.instrumentIdx);
    } catch (e) {
        console.warn('[Piano] Synth init failed:', e);
    }
}

async function _synthLoadInstrument(idx) {
    const inst = INSTRUMENTS[idx];
    if (!inst || !_synthPlayer || !_audioCtx) return;
    _synthLoading = true;
    const varName = _wafVar(inst.gm);

    try {
        if (!window[varName]) {
            await _loadScript(_wafUrl(inst.gm));
        }
        const preset = window[varName];
        if (preset) {
            _synthPlayer.adjustPreset(_audioCtx, preset);
            _synthPreset = preset;
        }
    } catch (e) {
        console.warn('[Piano] Failed to load instrument:', inst.name, e);
    }
    _synthLoading = false;
}

function _synthEnsureCtx() {
    if (_audioCtx && _audioCtx.state === 'suspended') {
        _audioCtx.resume();
    }
}

function _synthNoteOn(midi, velocity) {
    if (!_synthPlayer || !_synthPreset || !_audioCtx || !_synthGain) return;
    _synthEnsureCtx();

    // Cancel any existing envelope for this note
    const existing = _noteEnvelopes.get(midi);
    if (existing) { try { existing.cancel(); } catch (_) {} }

    const vol = (velocity / 127) * _cfg.synthVolume;
    const envelope = _synthPlayer.queueWaveTable(
        _audioCtx, _synthGain, _synthPreset, 0, midi, 999, vol
    );
    _noteEnvelopes.set(midi, envelope);
}

function _synthNoteOff(midi) {
    const env = _noteEnvelopes.get(midi);
    if (env) {
        try { env.cancel(); } catch (_) {}
        _noteEnvelopes.delete(midi);
    }
}

function _synthSetVolume(vol) {
    _saveCfg('synthVolume', vol);
    if (_synthGain) _synthGain.gain.value = vol;
}

// ═══════════════════════════════════════════════════════════════════════
// Web MIDI Input
// ═══════════════════════════════════════════════════════════════════════

async function _midiInit() {
    if (_midiAccess) return;
    if (!navigator.requestMIDIAccess) return;
    try {
        _midiAccess = await navigator.requestMIDIAccess({ sysex: false });
        _midiAccess.onstatechange = () => _midiUpdateDeviceList();
        _midiAutoConnect();
    } catch (e) {
        console.warn('[Piano] MIDI access denied:', e);
    }
}

function _midiAutoConnect() {
    if (!_midiAccess) return;
    const inputs = [];
    _midiAccess.inputs.forEach(inp => inputs.push(inp));
    if (!inputs.length) return;

    // Prefer saved device, fall back to first
    const saved = _cfg.midiInputId;
    const target = inputs.find(i => i.id === saved) || inputs[0];
    _midiConnect(target.id);
}

function _midiConnect(id) {
    // Disconnect previous
    if (_midiInput) _midiInput.onmidimessage = null;
    _midiInput = null;

    if (!_midiAccess) return;
    _midiAccess.inputs.forEach(inp => {
        if (inp.id === id) {
            _midiInput = inp;
            _midiInput.onmidimessage = _midiOnMessage;
            _saveCfg('midiInputId', id);
        }
    });
    _midiUpdateDeviceList();
}

function _midiOnMessage(e) {
    const [status, note, velocity] = e.data;
    const ch = status & 0x0F;

    // Channel filter (-1 = all)
    if (_cfg.midiChannel >= 0 && ch !== _cfg.midiChannel) return;

    const cmd = status & 0xF0;
    const transposed = note + _cfg.transpose;

    if (cmd === 0x90 && velocity > 0) {
        // Note On
        _onNoteOn(transposed, velocity);
    } else if (cmd === 0x80 || (cmd === 0x90 && velocity === 0)) {
        // Note Off
        _onNoteOff(transposed);
    } else if (cmd === 0xB0 && note === 64) {
        // Sustain pedal (CC#64)
        if (velocity >= 64) {
            _sustainOn = true;
        } else {
            _sustainOn = false;
            // Release all sustained notes
            for (const midi of _sustainedNotes) {
                _heldNotes.delete(midi);
                _synthNoteOff(midi);
            }
            _sustainedNotes.clear();
        }
    }
}

function _onNoteOn(midi, velocity) {
    if (midi < 0 || midi > 127) return;
    _heldNotes.set(midi, velocity);
    _synthNoteOn(midi, velocity);

    // Init audio context on first interaction
    _synthEnsureCtx();

    // Hit detection
    if (_cfg.hitDetection) {
        _checkHit(midi);
    }
}

function _onNoteOff(midi) {
    if (midi < 0 || midi > 127) return;
    if (_sustainOn) {
        _sustainedNotes.add(midi);
        return;
    }
    _heldNotes.delete(midi);
    _synthNoteOff(midi);
}

function _midiUpdateDeviceList() {
    const sel = document.getElementById('piano-midi-select');
    if (!sel || !_midiAccess) return;

    const inputs = [];
    _midiAccess.inputs.forEach(inp => inputs.push(inp));

    sel.innerHTML = '<option value="">None</option>' +
        inputs.map(inp => {
            const selected = _midiInput && _midiInput.id === inp.id ? 'selected' : '';
            return `<option value="${inp.id}" ${selected}>${inp.name}</option>`;
        }).join('');
}

// ═══════════════════════════════════════════════════════════════════════
// Hit Detection / Accuracy Scoring
// ═══════════════════════════════════════════════════════════════════════

function _checkHit(playedMidi) {
    const t = highway.getTime();
    const notes = highway.getNotes();
    const chords = highway.getChords();

    let foundHit = false;

    // Check standalone notes
    if (notes) {
        for (const n of notes) {
            if (n.t > t + HIT_TOLERANCE + 0.5) break;
            if (n.t < t - HIT_TOLERANCE - 0.5) continue;
            const songMidi = noteToMidi(n.s, n.f);
            const key = _noteKey(n.t, songMidi);
            if (songMidi === playedMidi && Math.abs(n.t - t) <= HIT_TOLERANCE && !_hitNoteKeys.has(key)) {
                _hitNoteKeys.add(key);
                foundHit = true;
                break;
            }
        }
    }

    // Check chord notes
    if (!foundHit && chords) {
        for (const c of chords) {
            if (c.t > t + HIT_TOLERANCE + 0.5) break;
            if (c.t < t - HIT_TOLERANCE - 0.5) continue;
            for (const cn of (c.notes || [])) {
                const songMidi = noteToMidi(cn.s, cn.f);
                const key = _noteKey(c.t, songMidi);
                if (songMidi === playedMidi && Math.abs(c.t - t) <= HIT_TOLERANCE && !_hitNoteKeys.has(key)) {
                    _hitNoteKeys.add(key);
                    foundHit = true;
                    break;
                }
            }
            if (foundHit) break;
        }
    }

    if (foundHit) {
        _hits++;
        _streak++;
        if (_streak > _bestStreak) _bestStreak = _streak;
    } else {
        _misses++;
        _streak = 0;
        _wrongFlashes.push({ midi: playedMidi, wall: performance.now() });
    }
}

function _updateMissedNotes(t) {
    if (!_cfg.hitDetection) return;
    const notes = highway.getNotes();
    const chords = highway.getChords();
    const cutoff = t - HIT_TOLERANCE - 0.05;

    if (notes) {
        for (const n of notes) {
            if (n.t > cutoff) break;
            if (n.t < cutoff - 2) continue;
            const songMidi = noteToMidi(n.s, n.f);
            const key = _noteKey(n.t, songMidi);
            if (!_hitNoteKeys.has(key) && !_missedNoteKeys.has(key) && n.t < cutoff) {
                _missedNoteKeys.add(key);
            }
        }
    }
    if (chords) {
        for (const c of chords) {
            if (c.t > cutoff) break;
            if (c.t < cutoff - 2) continue;
            for (const cn of (c.notes || [])) {
                const songMidi = noteToMidi(cn.s, cn.f);
                const key = _noteKey(c.t, songMidi);
                if (!_hitNoteKeys.has(key) && !_missedNoteKeys.has(key) && c.t < cutoff) {
                    _missedNoteKeys.add(key);
                }
            }
        }
    }

    // Prune old wrong flashes (>400ms)
    const now = performance.now();
    while (_wrongFlashes.length && now - _wrongFlashes[0].wall > 400) {
        _wrongFlashes.shift();
    }
}

function _resetScoring() {
    _hits = 0; _misses = 0; _streak = 0; _bestStreak = 0;
    _hitNoteKeys.clear();
    _missedNoteKeys.clear();
    _wrongFlashes.length = 0;
}

// ═══════════════════════════════════════════════════════════════════════
// Note Range Detection
// ═══════════════════════════════════════════════════════════════════════

function detectRange(notes, chords) {
    let lo = 127, hi = 0;
    if (notes) {
        for (const n of notes) {
            const m = noteToMidi(n.s, n.f);
            if (m < lo) lo = m;
            if (m > hi) hi = m;
        }
    }
    if (chords) {
        for (const c of chords) {
            for (const cn of (c.notes || [])) {
                const m = noteToMidi(cn.s, cn.f);
                if (m < lo) lo = m;
                if (m > hi) hi = m;
            }
        }
    }
    if (lo > hi) { lo = 48; hi = 84; }
    lo = Math.max(0, Math.floor(lo / 12) * 12);
    hi = Math.min(127, Math.ceil((hi + 1) / 12) * 12 - 1);
    while (hi - lo < 23) { hi = Math.min(127, hi + 12); }
    return { lo, hi };
}

// ═══════════════════════════════════════════════════════════════════════
// Auto-detection
// ═══════════════════════════════════════════════════════════════════════

const KEYS_PATTERNS = /keys|piano|keyboard|synth/i;

function isKeysArrangement() {
    const info = highway.getSongInfo();
    if (!info) return false;
    if (info.arrangement && KEYS_PATTERNS.test(info.arrangement)) return true;
    if (info.arrangements) {
        const idx = info.arrangement_index;
        const arr = info.arrangements.find(a => a.index === idx);
        if (arr && KEYS_PATTERNS.test(arr.name)) return true;
    }
    return false;
}

// ═══════════════════════════════════════════════════════════════════════
// Toggle Buttons
// ═══════════════════════════════════════════════════════════════════════

function _pianoInjectButton() {
    const controls = document.getElementById('player-controls');
    if (!controls || document.getElementById('btn-piano')) return;

    const closeBtn = controls.querySelector('button:last-child');

    // Piano toggle
    const btn = document.createElement('button');
    btn.id = 'btn-piano';
    btn.className = 'px-3 py-1.5 bg-dark-600 hover:bg-dark-500 rounded-lg text-xs text-gray-400 transition';
    btn.textContent = 'Piano';
    btn.title = 'Toggle piano highway view';
    btn.onclick = () => _pianoToggle(false);
    controls.insertBefore(btn, closeBtn);

    // Settings gear
    const gear = document.createElement('button');
    gear.id = 'btn-piano-settings';
    gear.className = 'px-2 py-1.5 bg-dark-600 hover:bg-dark-500 rounded-lg text-xs text-gray-500 transition hidden';
    gear.innerHTML = '&#9881;';
    gear.title = 'Piano settings (MIDI, sound, scoring)';
    gear.onclick = _toggleSettings;
    controls.insertBefore(gear, closeBtn);
}

function _pianoUpdateButton() {
    const btn = document.getElementById('btn-piano');
    const gear = document.getElementById('btn-piano-settings');
    if (btn) {
        if (_pianoEnabled) {
            btn.className = 'px-3 py-1.5 bg-indigo-900/50 rounded-lg text-xs text-indigo-300 transition';
            btn.textContent = 'Piano \u2713';
        } else {
            btn.className = 'px-3 py-1.5 bg-dark-600 hover:bg-dark-500 rounded-lg text-xs text-gray-400 transition';
            btn.textContent = 'Piano';
        }
    }
    if (gear) gear.classList.toggle('hidden', !_pianoEnabled);
}

function _pianoToggle(auto) {
    if (auto && _pianoEnabled && !_pianoAuto) return;
    _pianoEnabled = !_pianoEnabled || auto;
    _pianoAuto = auto && _pianoEnabled;
    _pianoUpdateButton();

    if (_pianoEnabled) {
        _pianoShow();
    } else {
        _pianoHide();
    }
}

// ═══════════════════════════════════════════════════════════════════════
// Settings Panel
// ═══════════════════════════════════════════════════════════════════════

function _toggleSettings() {
    _settingsVisible = !_settingsVisible;
    if (_settingsPanel) _settingsPanel.style.display = _settingsVisible ? '' : 'none';
    if (_settingsVisible) {
        _midiInit();
        _synthInit();
        _midiUpdateDeviceList();
    }
}

function _createSettingsPanel() {
    if (_settingsPanel) return;
    const player = document.getElementById('player');
    if (!player) return;

    const panel = document.createElement('div');
    panel.id = 'piano-settings-panel';
    panel.style.cssText = 'position:absolute;top:0;left:0;right:0;z-index:15;' +
        'background:rgba(8,8,20,0.94);border-bottom:1px solid #222;padding:6px 12px;' +
        'font-family:system-ui,sans-serif;display:none;';

    const channelOpts = '<option value="-1"' + (_cfg.midiChannel === -1 ? ' selected' : '') + '>All</option>' +
        Array.from({length: 16}, (_, i) =>
            `<option value="${i}"${_cfg.midiChannel === i ? ' selected' : ''}>${i + 1}</option>`
        ).join('');

    const instrumentOpts = INSTRUMENTS.map((inst, i) =>
        `<option value="${i}"${_cfg.instrumentIdx === i ? ' selected' : ''}>${inst.name}</option>`
    ).join('');

    panel.innerHTML = `
        <div style="display:flex;gap:14px;align-items:center;flex-wrap:wrap;">
            <div style="display:flex;align-items:center;gap:4px;">
                <span style="font-size:10px;color:#666;">MIDI</span>
                <select id="piano-midi-select" style="background:#1a1a2e;border:1px solid #333;border-radius:6px;
                    padding:3px 6px;font-size:11px;color:#ccc;outline:none;max-width:180px;">
                    <option value="">None</option>
                </select>
            </div>
            <div style="display:flex;align-items:center;gap:4px;">
                <span style="font-size:10px;color:#666;">Sound</span>
                <select id="piano-instrument-select" style="background:#1a1a2e;border:1px solid #333;border-radius:6px;
                    padding:3px 6px;font-size:11px;color:#ccc;outline:none;">
                    ${instrumentOpts}
                </select>
            </div>
            <div style="display:flex;align-items:center;gap:4px;">
                <span style="font-size:10px;color:#666;">Vol</span>
                <input type="range" id="piano-vol-slider" min="0" max="100"
                    value="${Math.round(_cfg.synthVolume * 100)}"
                    style="width:70px;accent-color:#6366f1;height:14px;">
            </div>
            <div style="display:flex;align-items:center;gap:4px;">
                <span style="font-size:10px;color:#666;">Ch</span>
                <select id="piano-channel-select" style="background:#1a1a2e;border:1px solid #333;border-radius:6px;
                    padding:3px 6px;font-size:11px;color:#ccc;outline:none;width:52px;">
                    ${channelOpts}
                </select>
            </div>
            <div style="display:flex;align-items:center;gap:3px;">
                <span style="font-size:10px;color:#666;">Transpose</span>
                <button id="piano-tr-down" style="background:#1a1a2e;border:1px solid #333;border-radius:4px;
                    width:20px;height:20px;color:#aaa;font-size:12px;cursor:pointer;line-height:1;">-</button>
                <span id="piano-tr-val" style="font-size:11px;color:#ccc;min-width:18px;text-align:center;">${_cfg.transpose}</span>
                <button id="piano-tr-up" style="background:#1a1a2e;border:1px solid #333;border-radius:4px;
                    width:20px;height:20px;color:#aaa;font-size:12px;cursor:pointer;line-height:1;">+</button>
            </div>
            <label style="display:flex;align-items:center;gap:3px;font-size:11px;color:#999;cursor:pointer;">
                <input type="checkbox" id="piano-chk-names" ${_cfg.showNoteNames ? 'checked' : ''}
                    style="accent-color:#6366f1;"> Notes
            </label>
            <label style="display:flex;align-items:center;gap:3px;font-size:11px;color:#999;cursor:pointer;">
                <input type="checkbox" id="piano-chk-hits" ${_cfg.hitDetection ? 'checked' : ''}
                    style="accent-color:#22cc66;"> Hits
            </label>
        </div>`;

    // Insert before canvas
    const controls = document.getElementById('player-controls');
    if (controls) {
        player.insertBefore(panel, controls);
    } else {
        player.appendChild(panel);
    }
    _settingsPanel = panel;

    // Wire up events
    panel.querySelector('#piano-midi-select').onchange = function () {
        _midiConnect(this.value);
        _synthInit();
    };
    panel.querySelector('#piano-instrument-select').onchange = async function () {
        const idx = parseInt(this.value);
        _saveCfg('instrumentIdx', idx);
        await _synthInit();
        await _synthLoadInstrument(idx);
    };
    panel.querySelector('#piano-vol-slider').oninput = function () {
        _synthSetVolume(parseInt(this.value) / 100);
    };
    panel.querySelector('#piano-channel-select').onchange = function () {
        _saveCfg('midiChannel', parseInt(this.value));
    };
    panel.querySelector('#piano-tr-down').onclick = function () {
        const v = Math.max(-12, _cfg.transpose - 1);
        _saveCfg('transpose', v);
        document.getElementById('piano-tr-val').textContent = v;
    };
    panel.querySelector('#piano-tr-up').onclick = function () {
        const v = Math.min(12, _cfg.transpose + 1);
        _saveCfg('transpose', v);
        document.getElementById('piano-tr-val').textContent = v;
    };
    panel.querySelector('#piano-chk-names').onchange = function () {
        _saveCfg('showNoteNames', this.checked);
    };
    panel.querySelector('#piano-chk-hits').onchange = function () {
        _saveCfg('hitDetection', this.checked);
        if (this.checked) _resetScoring();
    };
}

function _removeSettingsPanel() {
    if (_settingsPanel) {
        _settingsPanel.remove();
        _settingsPanel = null;
    }
    _settingsVisible = false;
}

// ═══════════════════════════════════════════════════════════════════════
// Canvas Management
// ═══════════════════════════════════════════════════════════════════════

function _pianoShow() {
    const hwCanvas = document.getElementById('highway-canvas');
    if (hwCanvas) hwCanvas.style.display = 'none';

    if (!_pianoCanvas) {
        const player = document.getElementById('player');
        if (!player) return;

        _pianoCanvas = document.createElement('canvas');
        _pianoCanvas.id = 'piano-highway-canvas';
        _pianoCanvas.style.cssText = 'position:absolute;top:0;left:0;width:100%;height:100%;z-index:5;';

        const controls = document.getElementById('player-controls');
        if (controls) {
            player.insertBefore(_pianoCanvas, controls);
        } else {
            player.appendChild(_pianoCanvas);
        }
        _pianoCtx = _pianoCanvas.getContext('2d');
    }

    _createSettingsPanel();
    _pianoResize();
    window.addEventListener('resize', _pianoResize);
    if (!_rafId) _rafId = requestAnimationFrame(_pianoDraw);

    // Auto-init MIDI and synth in background
    _midiInit();
    _synthInit();
}

function _pianoHide() {
    const hwCanvas = document.getElementById('highway-canvas');
    if (hwCanvas) hwCanvas.style.display = '';

    if (_pianoCanvas) {
        window.removeEventListener('resize', _pianoResize);
        _pianoCanvas.remove();
        _pianoCanvas = null;
        _pianoCtx = null;
    }
    if (_rafId) {
        cancelAnimationFrame(_rafId);
        _rafId = null;
    }
    _removeSettingsPanel();
}

function _pianoResize() {
    if (!_pianoCanvas) return;
    const player = document.getElementById('player');
    if (!player) return;
    const dpr = window.devicePixelRatio || 1;
    _pianoCanvas.width = player.clientWidth * dpr;
    _pianoCanvas.height = player.clientHeight * dpr;
    _pianoCanvas.style.width = player.clientWidth + 'px';
    _pianoCanvas.style.height = player.clientHeight + 'px';
    if (_pianoCtx) _pianoCtx.setTransform(dpr, 0, 0, dpr, 0, 0);
}

// ═══════════════════════════════════════════════════════════════════════
// Keyboard Geometry
// ═══════════════════════════════════════════════════════════════════════

function buildKeyLayout(lo, hi, areaX, areaW) {
    const keys = [];
    let whiteCount = 0;
    for (let m = lo; m <= hi; m++) {
        if (!isBlackKey(m)) whiteCount++;
    }
    if (whiteCount === 0) return keys;

    const whiteW = areaW / whiteCount;
    const blackW = whiteW * 0.6;

    let wx = areaX;
    for (let m = lo; m <= hi; m++) {
        if (!isBlackKey(m)) {
            keys.push({ midi: m, x: wx, w: whiteW, black: false });
            wx += whiteW;
        }
    }
    for (let m = lo; m <= hi; m++) {
        if (!isBlackKey(m)) continue;
        const prevWhite = keys.find(k => !k.black && k.midi === m - 1);
        if (prevWhite) {
            keys.push({ midi: m, x: prevWhite.x + prevWhite.w - blackW / 2, w: blackW, black: true });
        }
    }
    return keys;
}

function keyForMidi(midi, layout) {
    for (const k of layout) {
        if (k.midi === midi) return k;
    }
    return null;
}

// ═══════════════════════════════════════════════════════════════════════
// Drawing
// ═══════════════════════════════════════════════════════════════════════

let _cachedRange = null;
let _cachedLayout = null;
let _lastLayoutW = 0;

function _pianoDraw() {
    _rafId = requestAnimationFrame(_pianoDraw);
    if (!_pianoCanvas || !_pianoCtx) return;

    const notes = highway.getNotes();
    const chords = highway.getChords();
    const t = highway.getTime();

    if (!notes && !chords) return;

    const W = _pianoCanvas.width / (window.devicePixelRatio || 1);
    const H = _pianoCanvas.height / (window.devicePixelRatio || 1);
    const ctx = _pianoCtx;

    if (!_cachedRange) _cachedRange = detectRange(notes, chords);
    const { lo, hi } = _cachedRange;

    const kbH = H * KEYBOARD_H_FRAC;
    const kbTop = H - kbH;
    const padL = 10, padR = 10;

    if (!_cachedLayout || _lastLayoutW !== W) {
        _cachedLayout = buildKeyLayout(lo, hi, padL, W - padL - padR);
        _lastLayoutW = W;
    }
    const layout = _cachedLayout;

    // Update missed notes tracking
    _updateMissedNotes(t);

    // ── Background ──────────────────────────────────────────────────
    ctx.fillStyle = '#060610';
    ctx.fillRect(0, 0, W, H);

    // ── Note lane guides ────────────────────────────────────────────
    const noteAreaTop = 0;
    const nowLineY = kbTop * NOW_LINE_Y_FRAC;

    ctx.globalAlpha = 0.08;
    for (const k of layout) {
        if (k.black) continue;
        ctx.fillStyle = '#ffffff';
        ctx.fillRect(k.x, noteAreaTop, k.w, kbTop);
        ctx.fillStyle = '#222244';
        ctx.fillRect(k.x + k.w - 0.5, noteAreaTop, 1, kbTop);
    }
    ctx.globalAlpha = 1;

    // ── Beat lines ──────────────────────────────────────────────────
    const beats = highway.getBeats();
    if (beats) {
        for (const b of beats) {
            const dt = b.time - t;
            if (dt < -0.1 || dt > VISIBLE_SECONDS) continue;
            const y = _timeToY(dt, nowLineY, noteAreaTop);
            ctx.strokeStyle = b.measure > 0 ? 'rgba(255,255,255,0.15)' : 'rgba(255,255,255,0.06)';
            ctx.lineWidth = b.measure > 0 ? 1 : 0.5;
            ctx.beginPath();
            ctx.moveTo(padL, y);
            ctx.lineTo(W - padR, y);
            ctx.stroke();
        }
    }

    // ── Now line ────────────────────────────────────────────────────
    ctx.strokeStyle = '#ffffff';
    ctx.lineWidth = 2;
    ctx.globalAlpha = 0.5;
    ctx.beginPath();
    ctx.moveTo(padL, nowLineY);
    ctx.lineTo(W - padR, nowLineY);
    ctx.stroke();
    ctx.globalAlpha = 1;

    // ── Scrolling notes ─────────────────────────────────────────────
    _drawScrollingNotes(ctx, notes, chords, t, layout, noteAreaTop, nowLineY);

    // ── Keyboard ────────────────────────────────────────────────────
    _drawKeyboard(ctx, layout, kbTop, kbH, notes, chords, t);

    // ── Accuracy HUD ────────────────────────────────────────────────
    if (_cfg.hitDetection && (_hits + _misses) > 0) {
        _drawAccuracyHUD(ctx, W);
    }

    // ── MIDI status indicator ───────────────────────────────────────
    if (_midiInput) {
        ctx.fillStyle = '#22cc66';
        ctx.beginPath();
        ctx.arc(W - 20, 16, 4, 0, Math.PI * 2);
        ctx.fill();
        ctx.fillStyle = '#22cc6688';
        ctx.font = '9px sans-serif';
        ctx.textAlign = 'right';
        ctx.textBaseline = 'middle';
        ctx.fillText('MIDI', W - 28, 16);
    }
}

function _timeToY(dt, nowLineY, topY) {
    if (dt <= 0) return nowLineY + (-dt / 0.3) * 20;
    const frac = dt / VISIBLE_SECONDS;
    return nowLineY - frac * (nowLineY - topY);
}

// ── Scrolling Notes ─────────────────────────────────────────────────

function _drawScrollingNotes(ctx, notes, chords, t, layout, topY, nowLineY) {
    const allNotes = [];

    if (notes) {
        for (const n of notes) {
            const dt = n.t - t;
            if (dt > VISIBLE_SECONDS + 1) break;
            if (dt < -1 && (n.t + (n.sus || 0)) < t - 0.5) continue;
            allNotes.push({ midi: noteToMidi(n.s, n.f), t: n.t, sus: n.sus || 0, accent: n.ac });
        }
    }
    if (chords) {
        for (const c of chords) {
            const dt = c.t - t;
            if (dt > VISIBLE_SECONDS + 1) break;
            if (dt < -1) continue;
            for (const cn of (c.notes || [])) {
                allNotes.push({ midi: noteToMidi(cn.s, cn.f), t: c.t, sus: cn.sus || 0, accent: cn.ac });
            }
        }
    }

    for (const n of allNotes) {
        const key = keyForMidi(n.midi, layout);
        if (!key) continue;

        const dt = n.t - t;
        const dtEnd = (n.t + n.sus) - t;

        const yBottom = _timeToY(dt, nowLineY, topY);
        const yTop = n.sus > 0.05 ? _timeToY(Math.max(dt, dtEnd), nowLineY, topY) : yBottom - 8;

        const y1 = Math.max(topY, Math.min(yTop, yBottom));
        const y2 = Math.min(nowLineY + 10, Math.max(yTop, yBottom));
        const noteH = y2 - y1;
        if (noteH < 1) continue;

        const isActive = dt <= 0.05 && dtEnd >= -0.05;

        // Determine color based on hit state
        let color;
        const nk = _noteKey(n.t, n.midi);
        if (_cfg.hitDetection && _hitNoteKeys.has(nk)) {
            color = COL_HIT;
        } else if (_cfg.hitDetection && _missedNoteKeys.has(nk)) {
            color = COL_MISSED;
        } else {
            color = noteColor(n.midi, isActive);
        }

        const barX = key.x + 1;
        const barW = key.w - 2;

        if (isActive) {
            ctx.shadowColor = color;
            ctx.shadowBlur = 12;
        }

        ctx.fillStyle = color;
        const radius = Math.min(3, barW / 4, noteH / 2);
        _roundRect(ctx, barX, y1, barW, noteH, radius);
        ctx.fill();
        ctx.shadowBlur = 0;

        // Note label
        if (_cfg.showNoteNames && noteH >= NOTE_LABEL_MIN_H && barW >= 14) {
            ctx.fillStyle = '#000';
            ctx.font = `bold ${Math.min(10, barW * 0.5)}px sans-serif`;
            ctx.textAlign = 'center';
            ctx.textBaseline = 'middle';
            ctx.fillText(midiToNoteName(n.midi), barX + barW / 2, y1 + noteH / 2);
        }
    }
}

// ── Keyboard Drawing ────────────────────────────────────────────────

function _drawKeyboard(ctx, layout, kbTop, kbH, notes, chords, t) {
    // Build per-key state: song active, player pressed, hit/wrong
    const songActiveSet = new Set();
    const window_ = 0.06;
    if (notes) {
        for (const n of notes) {
            if (n.t > t + window_) continue;
            const end = n.t + (n.sus || 0);
            if (end < t - window_) continue;
            if (n.t <= t + window_ && end >= t - window_) {
                songActiveSet.add(noteToMidi(n.s, n.f));
            }
        }
    }
    if (chords) {
        for (const c of chords) {
            if (c.t > t + window_) continue;
            if (c.t < t - 1) continue;
            for (const cn of (c.notes || [])) {
                const end = c.t + (cn.sus || 0);
                if (c.t <= t + window_ && end >= t - window_) {
                    songActiveSet.add(noteToMidi(cn.s, cn.f));
                }
            }
        }
    }

    // Wrong flash set
    const wrongSet = new Set();
    const now = performance.now();
    for (const wf of _wrongFlashes) {
        if (now - wf.wall < 400) wrongSet.add(wf.midi);
    }

    // Background
    ctx.fillStyle = '#0a0a18';
    ctx.fillRect(0, kbTop, ctx.canvas.width / (window.devicePixelRatio || 1), kbH + 2);

    const blackH = kbH * 0.6;

    // Draw white keys
    for (const k of layout) {
        if (k.black) continue;
        const songActive = songActiveSet.has(k.midi);
        const playerHeld = _heldNotes.has(k.midi);
        const isWrong = wrongSet.has(k.midi);

        let fill;
        if (playerHeld && songActive) {
            fill = COL_HIT;
        } else if (isWrong && playerHeld) {
            fill = COL_WRONG;
        } else if (playerHeld) {
            fill = COL_PLAYER;
        } else if (songActive) {
            fill = COL_SONG_ACTIVE;
        } else {
            fill = '#e8e8f0';
        }

        ctx.fillStyle = fill;
        ctx.fillRect(k.x, kbTop, k.w - 1, kbH);
        ctx.strokeStyle = '#888';
        ctx.lineWidth = 0.5;
        ctx.strokeRect(k.x, kbTop, k.w - 1, kbH);

        // C labels
        if (k.midi % 12 === 0) {
            const octave = Math.floor(k.midi / 12) - 1;
            ctx.fillStyle = (playerHeld || songActive) ? '#000' : '#888';
            ctx.font = '9px sans-serif';
            ctx.textAlign = 'center';
            ctx.textBaseline = 'bottom';
            ctx.fillText('C' + octave, k.x + k.w / 2, kbTop + kbH - 2);
        }
    }

    // Draw black keys
    for (const k of layout) {
        if (!k.black) continue;
        const songActive = songActiveSet.has(k.midi);
        const playerHeld = _heldNotes.has(k.midi);
        const isWrong = wrongSet.has(k.midi);

        let fill;
        if (playerHeld && songActive) {
            fill = COL_HIT;
        } else if (isWrong && playerHeld) {
            fill = COL_WRONG;
        } else if (playerHeld) {
            fill = COL_PLAYER;
        } else if (songActive) {
            fill = COL_SONG_ACTIVE;
        } else {
            fill = '#1a1a2e';
        }

        ctx.fillStyle = fill;
        ctx.fillRect(k.x, kbTop, k.w, blackH);
        ctx.strokeStyle = (playerHeld || songActive) ? '#ffffff44' : '#333';
        ctx.lineWidth = 0.5;
        ctx.strokeRect(k.x, kbTop, k.w, blackH);

        if (playerHeld || songActive) {
            ctx.shadowColor = fill;
            ctx.shadowBlur = 8;
            ctx.fillRect(k.x, kbTop, k.w, blackH);
            ctx.shadowBlur = 0;
        }
    }
}

// ── Accuracy HUD ────────────────────────────────────────────────────

function _drawAccuracyHUD(ctx, W) {
    const total = _hits + _misses;
    const pct = total > 0 ? Math.round((_hits / total) * 100) : 0;

    const hudY = 10;
    const hudH = 22;
    const text = `Accuracy: ${pct}%   Streak: ${_streak}   Best: ${_bestStreak}   ${_hits}/${total}`;

    ctx.font = 'bold 11px sans-serif';
    const tw = ctx.measureText(text).width;
    const hudX = (W - tw) / 2 - 12;
    const hudW = tw + 24;

    ctx.fillStyle = 'rgba(8,8,20,0.75)';
    _roundRect(ctx, hudX, hudY, hudW, hudH, 6);
    ctx.fill();

    ctx.fillStyle = pct >= 80 ? '#22cc66' : pct >= 50 ? '#ffcc33' : '#ff6644';
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    ctx.fillText(text, W / 2, hudY + hudH / 2);
}

// ── Round Rect Helper ───────────────────────────────────────────────

function _roundRect(ctx, x, y, w, h, r) {
    ctx.beginPath();
    ctx.moveTo(x + r, y);
    ctx.lineTo(x + w - r, y);
    ctx.quadraticCurveTo(x + w, y, x + w, y + r);
    ctx.lineTo(x + w, y + h - r);
    ctx.quadraticCurveTo(x + w, y + h, x + w - r, y + h);
    ctx.lineTo(x + r, y + h);
    ctx.quadraticCurveTo(x, y + h, x, y + h - r);
    ctx.lineTo(x, y + r);
    ctx.quadraticCurveTo(x, y, x + r, y);
    ctx.closePath();
}

// ═══════════════════════════════════════════════════════════════════════
// Hook into playSong
// ═══════════════════════════════════════════════════════════════════════

function _pianoOnSongLoad() {
    _pianoInjectButton();
    _cachedRange = null;
    _cachedLayout = null;
    _resetScoring();

    setTimeout(() => {
        if (isKeysArrangement()) {
            _pianoToggle(true);
        } else if (_pianoAuto) {
            _pianoEnabled = false;
            _pianoAuto = false;
            _pianoHide();
            _pianoUpdateButton();
        }
    }, 500);
}

const _origPlaySong = window.playSong;
window.playSong = async function (filename, arrangement) {
    if (_pianoAuto) {
        _pianoEnabled = false;
        _pianoAuto = false;
        _pianoHide();
    }
    await _origPlaySong(filename, arrangement);
    _pianoOnSongLoad();
};

const _origReconnect = highway.reconnect.bind(highway);
highway.reconnect = function (filename, arrangement) {
    _cachedRange = null;
    _cachedLayout = null;
    _resetScoring();
    _origReconnect(filename, arrangement);
    setTimeout(() => {
        if (isKeysArrangement()) {
            if (!_pianoEnabled) _pianoToggle(true);
        } else if (_pianoAuto) {
            _pianoEnabled = false;
            _pianoAuto = false;
            _pianoHide();
            _pianoUpdateButton();
        }
    }, 500);
};

})();
