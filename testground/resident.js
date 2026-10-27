// resident.js — the Bell's resident in the tab (Web.Sim.Resident, CLIENT-54). The kernel runs the
// deployed resident's tick (Hosting.Resident.tickP, with its two holes filled by Hosting.Resident.fill)
// and stops at each effect. This file performs the effect and hands the result back:
//   a member command: run as the resident's member, through the page's client;
//   an ask: the demo's scripted answer for the ring's text (no model is called in the tab);
//   keep, forget, note: the tab's volume, which always holds;
//   say: one log line.
// It decides nothing about the queue; it only parses the kernel's lines.

import { unhex, names } from './nd.js';

const enc = new TextEncoder(), dec = new TextDecoder();
const u32 = (n) => { const o = new Uint8Array(4); new DataView(o.buffer).setUint32(0, n, true); return o; };
const cat = (...bs) => { const o = new Uint8Array(bs.reduce((a, b) => a + b.length, 0)); let i = 0; for (const b of bs) { o.set(b, i); i += b.length; } return o; };
const text = (h) => dec.decode(unhex(h));

// a ring as the kernel prints it: `NB RINGER TEXT [via V target T]`
export function ringOf(words) {
  const r = { notBefore: words[0], ringer: words[1], text: text(words[2]) };
  const v = words.indexOf('via'); if (v > 0) { r.via = words[v + 1]; r.target = words[v + 3]; }
  return r;
}
function candOf(w) {   // `cand ask RING… usable` / `cand idle usable` / `cand withdraw CELL blocked` …
  const usable = w.at(-1) === 'usable';
  const kind = w[1], raw = w.slice(1, -1).join(' ');
  if (kind === 'ask' || kind === 'answer') return { kind, raw, ring: ringOf(w.slice(2, -1)), usable, supports: [] };
  if (kind === 'withdraw') return { kind, raw, cell: w[2], usable, supports: [] };
  return { kind, raw, usable, supports: [] };
}

// one tick: `run(argv)` runs a member command and returns { exit, stdout, stderr }; `answer(ringText)`
// returns the scripted text (or null: the ask is not sent). Returns the tick's events in order:
// { hole }, { cmd }, { ask }, { keep }, { forget }, { note }, { say }, then { end, memory }.
export async function residentTick(K, { run, answer, onEvent = () => {} }) {
  const N = names(K.table);
  const OK = N.status.ok;
  const events = [];
  const emit = (e) => { events.push(e); onEvent(e); };
  let r = K.resTick();
  for (let fuel = 256; fuel > 0; fuel--) {
    if (r[0] !== OK) { const e = { end: 'refused', why: dec.decode(r.slice(1)), memory: [] }; emit(e); return events; }
    const lines = dec.decode(r.slice(1)).replace(/\n$/, '').split('\n');
    let hole = null, i = 0;
    for (; i < lines.length; i++) {
      const w = lines[i].split(' ');
      if (w[0] === 'hole') {
        hole = { hole: w[1], cands: [] };
        if (w[1] === 'use') { const k = w.indexOf('refused'); hole.ring = ringOf(w.slice(2, k)); hole.line = text(w[k + 1]); }
      } else if (w[0] === 'cand') hole.cands.push(candOf(w));
      else if (w[0] === 'support') hole.cands.at(-1).supports.push({ fact: w.slice(1, -1).join(' '), holds: w.at(-1) === 'holds' });
      else if (w[0] === 'chose') {
        hole.chose = w.slice(1).join(' ');
        for (const c of hole.cands) c.chosen = c.raw === hole.chose;
        emit(hole); hole = null;
      }
      else break;
    }
    const w = (lines[i] ?? '').split(' ');
    if (w[0] === 'end') {
      const memory = lines.slice(i + 1).map((l) => { const x = l.split(' '); return x[0] === 'kept' ? { kept: ringOf(x.slice(1, -1)) } : { withdrawn: ringOf(x.slice(1, -1)), cell: x.at(-1) }; });
      emit({ end: w[1], why: w.slice(2).join(' '), memory });
      return events;
    }
    if (w[0] !== 'op') { emit({ end: 'refused', why: `unread line ${lines[i]}`, memory: [] }); return events; }
    let result;
    switch (w[1]) {
      case 'cmd': {
        const argv = w.slice(2).map(text);
        const o = await run(argv);
        emit({ cmd: argv, exit: o.exit, stdout: o.stdout, stderr: o.stderr });
        // a reply the client could not get is a transport failure, as on the member socket
        result = o.exit === 'client' ? cat(Uint8Array.of(0), enc.encode(o.stderr.trim()))
          : cat(Uint8Array.of(1), u32(N.exit[o.exit]), u32(enc.encode(o.stdout).length), enc.encode(o.stdout), enc.encode(o.stderr));
        break;
      }
      case 'ask': {
        const ring = ringOf(w.slice(2));
        const t = answer(ring.text);
        emit({ ask: ring, answer: t });
        result = t == null ? cat(Uint8Array.of(1), enc.encode('noAnswer')) : cat(Uint8Array.of(0), enc.encode(t));
        break;
      }
      case 'keep': emit({ keep: ringOf(w.slice(2, -1)), text: text(w.at(-1)) }); result = Uint8Array.of(1); break;
      case 'forget': emit({ forget: true }); result = Uint8Array.of(1); break;
      case 'note': emit({ note: +w[2] }); result = Uint8Array.of(1); break;
      case 'say': emit({ say: `resident: ${text(w[2] ?? '')}` }); result = new Uint8Array(0); break;
      default: emit({ end: 'refused', why: `unknown effect ${w[1]}`, memory: [] }); return events;
    }
    r = K.resAnswer(result);
  }
  emit({ end: 'refused', why: 'too many effects in one tick', memory: [] });
  return events;
}

// a tick's events as the text a demo step checks (`says`): the log lines, each hole's choice, how it ended
export function tickText(events) {
  return events.map((e) => (e.say ? e.say : e.hole ? `${e.hole}: chose ${choiceText(e)}` : e.end ? `end ${e.end} ${e.why}`.trim() : '')).filter(Boolean).join('\n') + '\n';
}

// a hole's choice in words: `ask "TEXT"`, `withdraw CELL`, `idle`, …
export function choiceText(h) {
  const c = h.cands.find((x) => x.chosen);
  if (!c) return h.chose;
  return c.ring ? `${c.kind} "${c.ring.text}"` : c.cell ? `${c.kind} ${c.cell}` : c.kind;
}

// the resident as a demo runs it (demos.js `start` and `tick` steps): `run(m, argv)` runs one member
// command and returns its result; `onEvent(m, e)` sees each event as it happens
export function residentDriver(K, run, onEvent = () => {}) {
  const OK = names(K.table).status.ok;
  return {
    async start(m, [bell, grant]) {
      const r = K.resStart(unhex(bell), unhex(grant));
      const said = dec.decode(r.slice(1));
      onEvent(m, { start: r[0] === OK ? said.trim() : `refused ${said}` });
      return r[0] === OK ? { exit: 'ok', stdout: said, stderr: '' } : { exit: 'refused', stdout: '', stderr: `refused ${said}\n` };
    },
    async tick(m, answers) {
      const events = await residentTick(K, { run: (argv) => run(m, argv), answer: (t) => answers[t] ?? null, onEvent: (e) => onEvent(m, e) });
      const end = events.at(-1);
      return { exit: end.end === 'next' ? 'ok' : 'refused', stdout: tickText(events), stderr: end.end === 'next' ? '' : `${end.end} ${end.why}\n`, events };
    },
  };
}
