'use strict';

/*
  Servidor do Gartic Listening.
  Sala única, até 25 jogadores. A sala (partida em andamento) fica na memória; as contas, moedas,
  níveis, conquistas e recordes ficam no banco (Supabase) para não se perder quando o servidor reinicia.

  Variáveis de ambiente:
    ALLOWED_ORIGIN  endereço do site (ex.: https://seuusuario.github.io). Pode ter vários, separados por vírgula.
                    Sem ela, qualquer site pode conectar (útil para testar no seu computador).
    SUPABASE_URL    endereço do projeto no Supabase (ex.: https://abcd.supabase.co).
    SUPABASE_KEY    chave "service_role" do Supabase (secreta, só no servidor).
                    Sem as duas, os dados vão para um arquivo local (somem se o servidor reiniciar na hospedagem grátis).
    ADMIN_KEY       senha sua para zerar o PIN de alguém: /admin/reset-pin?nick=NOME&key=SUA_SENHA
                    e para apagar um desenho da galeria: /admin/gallery-delete?id=NUMERO&key=SUA_SENHA
*/

const http = require('http');
const crypto = require('crypto');
const fs = require('fs');
const path = require('path');
const { Server } = require('socket.io');

const PORT = Number(process.env.PORT) || 3000;
const MAX_PLAYERS = 25;
const GRACE_MS = 20000;   // tempo para quem caiu voltar com o mesmo apelido sem perder pontos
// Salão de fliperama: mesmo mapa do cliente (gerado a partir dele).
const HALL = {"W":22,"H":16,"blocked":[[3,0],[4,0],[6,0],[7,0],[9,0],[10,0],[12,0],[13,0],[18,0],[0,2],[21,2],[0,3],[16,3],[17,3],[0,4],[16,4],[17,4],[0,5],[0,6],[10,6],[11,6],[12,6],[0,7],[10,7],[11,7],[12,7],[0,8],[10,8],[11,8],[12,8],[0,9],[16,10],[17,10],[4,11],[5,11],[16,11],[17,11],[4,12],[5,12],[21,13],[2,15],[19,7],[20,7],[20,10],[5,4],[6,4]],"spots":[[1,2,"pinball"],[1,3,"breakout"],[1,4,"cobrinha"],[1,5,"invasores"],[1,6,"blocos"],[1,7,"asteroides"],[1,8,"corrida"],[1,9,"memoria"],[3,1,"pong"],[4,1,"pong"],[6,1,"hoquei"],[7,1,"hoquei"],[9,1,"ligue4"],[10,1,"ligue4"],[12,1,"naval"],[13,1,"naval"],[9,6,"gartic"],[13,6,"gartic"],[9,7,"gartic"],[13,7,"gartic"],[9,8,"gartic"],[13,8,"gartic"],[9,9,"gartic"],[10,9,"gartic"],[11,9,"gartic"],[12,9,"gartic"],[13,9,"gartic"],[15,5,"quiz"],[16,5,"quiz"],[17,5,"quiz"],[18,5,"quiz"],[15,6,"quiz"],[16,6,"quiz"],[17,6,"quiz"],[18,6,"quiz"],[15,7,"quiz"],[16,7,"quiz"],[17,7,"quiz"],[18,7,"quiz"],[15,9,"batata"],[16,9,"batata"],[17,9,"batata"],[18,9,"batata"],[15,10,"batata"],[18,10,"batata"],[15,11,"batata"],[18,11,"batata"],[15,12,"batata"],[16,12,"batata"],[17,12,"batata"],[18,12,"batata"],[3,10,"arena"],[4,10,"arena"],[5,10,"arena"],[6,10,"arena"],[3,11,"arena"],[6,11,"arena"],[3,12,"arena"],[6,12,"arena"],[3,13,"arena"],[4,13,"arena"],[5,13,"arena"],[6,13,"arena"],[18,1,"jukebox"],[19,8],[20,8],[19,10],[20,11],[5,5],[6,5]],"spawn":[[8,12],[9,12],[10,12],[11,12],[12,12],[13,12],[8,13],[9,13],[10,13],[11,13],[12,13],[13,13],[8,14],[9,14],[10,14],[11,14],[12,14],[13,14],[8,15],[9,15],[10,15],[11,15],[12,15],[13,15]]};
const ROOM_W = HALL.W, ROOM_H = HALL.H;
const BLOCKSET = new Set(HALL.blocked.map(function (t) { return t[0] + ',' + t[1]; }));
const SPOTSET = new Set(HALL.spots.map(function (t) { return t[0] + ',' + t[1]; }));
function isBlocked(x, y) { return BLOCKSET.has(x + ',' + y); }
// vagas (frente dos fliperamas e ao redor das mesas) só cabem uma pessoa
function spotTaken(x, y, except) {
  return SPOTSET.has(x + ',' + y) && room.players.some(function (q) { return q !== except && q.x === x && q.y === y; });
}
const REACTS = 8;         // quantidade de reações disponíveis
const BETWEEN_S = 8;      // pausa entre rodadas
const ALLOWED = (process.env.ALLOWED_ORIGIN || '')
  .split(',')
  .map(function (s) { return s.trim().replace(/\/+$/, ''); })
  .filter(Boolean);

/* ---------- estado da sala ---------- */

const room = newRoom();

function newRoom() {
  return {
    phase: 'lobby',        // lobby | round | between
    players: [],           // { nick, key, id, online, score, gain, guessed, offTimer, lastMsg }
    cfg: null,             // { key, nome, total, seconds, words }
    n: 0,
    order: [],             // chaves (apelido em minúsculas) na ordem de quem desenha
    turn: -1,
    drawer: null,
    word: '',
    revealed: new Set(),
    mask: '',
    endAt: 0,
    actions: [],
    cur: null,
    bag: [],
    timer: null,
    nextTimer: null
  };
}

function resetRoom() {
  clearTimers();
  const fresh = newRoom();
  Object.keys(fresh).forEach(function (k) { room[k] = fresh[k]; });
}

function clearTimers() {
  if (room.timer) { clearInterval(room.timer); room.timer = null; }
  if (room.nextTimer) { clearTimeout(room.nextTimer); room.nextTimer = null; }
}

/* ---------- utilidades ---------- */

function shuffle(a) {
  for (let i = a.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    const t = a[i]; a[i] = a[j]; a[j] = t;
  }
  return a;
}

function norm(s) {
  return String(s || '')
    .normalize('NFD').replace(/\p{M}/gu, '')
    .toLowerCase()
    .replace(/[^\p{L}\p{N}]+/gu, ' ')
    .trim();
}

function lev(a, b) {
  if (a === b) return 0;
  if (Math.abs(a.length - b.length) > 1) return 2;
  const prev = [];
  for (let j = 0; j <= b.length; j++) prev[j] = j;
  for (let i = 1; i <= a.length; i++) {
    let last = prev[0];
    prev[0] = i;
    for (let j = 1; j <= b.length; j++) {
      const tmp = prev[j];
      prev[j] = Math.min(prev[j] + 1, prev[j - 1] + 1, last + (a[i - 1] === b[j - 1] ? 0 : 1));
      last = tmp;
    }
  }
  return prev[b.length];
}

function cleanNick(v) { return String(v || '').replace(/\s+/g, ' ').trim(); }
function nickError(n) {
  if (n.length < 2) return 'Escolha um apelido com pelo menos 2 caracteres.';
  if (n.length > 14) return 'Use no máximo 14 caracteres.';
  if (!/^[\p{L}\p{N} _.\-]+$/u.test(n)) return 'Use só letras, números, espaço, ponto, hífen ou sublinhado.';
  return '';
}

/* avatar: 15 números (pele, cabelo, ... fundo) separados por ponto; limites iguais aos do cliente */
const AV_LIMITS = [11, 16, 14, 8, 9, 11, 10, 18, 9, 9, 5, 12, 12, 12, 7];
function cleanAvatar(v) {
  if (typeof v !== 'string' || !/^\d{1,2}(\.\d{1,2}){14}$/.test(v)) return '';
  const a = v.split('.').map(Number);
  for (let i = 0; i < AV_LIMITS.length; i++) if (a[i] >= AV_LIMITS[i]) return '';
  return a.join('.');
}
function avatarTaken(av, exceptKey) {
  return room.players.some(function (p) { return p.av && p.av === av && p.key !== exceptKey; });
}
function takenList() { return room.players.filter(function (p) { return p.av; }).map(function (p) { return { k: p.av, n: p.nick }; }); }

function newStats() { return { hits: 0, misses: 0, fast: null, drawnHits: 0, mystery: 0, reacts: 0 }; }
function freeTile() {
  const free = HALL.spawn.filter(function (t) { return !room.players.some(function (q) { return q.x === t[0] && q.y === t[1]; }); });
  if (free.length) { const t = free[Math.floor(Math.random() * free.length)]; return { x: t[0], y: t[1] }; }
  for (let i = 0; i < 60; i++) {
    const x = 8 + Math.floor(Math.random() * 6), y = 12 + Math.floor(Math.random() * 4);
    if (!isBlocked(x, y) && !SPOTSET.has(x + ',' + y)) return { x: x, y: y };
  }
  return { x: 11, y: 14 };
}

function playerByKey(key) { return room.players.find(function (p) { return p.key === key; }) || null; }
function playerOf(socket) { return socket.data && socket.data.key ? playerByKey(socket.data.key) : null; }
function onlinePlayers() { return room.players.filter(function (p) { return p.online; }); }

/* ---------- fliperama: presença (JOGANDO) e partidas em dupla ---------- */
const SOLO_IDS = new Set(['pinball', 'breakout', 'cobrinha', 'invasores', 'blocos', 'asteroides', 'corrida', 'memoria']);
const DUO_IDS = new Set(['pong', 'hoquei', 'ligue4', 'naval']);
const duoWait = {};

function setPl(p, id) {
  id = String(id || '').slice(0, 16);
  if (id && !SOLO_IDS.has(id) && !DUO_IDS.has(id)) id = '';
  if (room.phase !== 'lobby') id = '';
  if ((p.pl || '') === id) return;
  p.pl = id;
  sendPlayers();
}
function duoCancelWait(p) {
  if (p.duoWait && duoWait[p.duoWait] === p.key) delete duoWait[p.duoWait];
  p.duoWait = '';
}
function duoLeave(p) {
  duoCancelWait(p);
  if (p.duoWith) {
    const q = playerByKey(p.duoWith);
    p.duoWith = '';
    if (q && q.duoWith === p.key) { q.duoWith = ''; if (q.id) io.to(q.id).emit('duo_gone'); }
  }
}
function endAllDuos() {
  room.players.forEach(function (p) { p.pl = ''; if (p.duoWith || p.duoWait) duoLeave(p); });
}

function publicPlayers() {
  return room.players.map(function (p) {
    return {
      nick: p.nick,
      av: p.av || '',
      x: p.x,
      y: p.y,
      score: p.score,
      online: p.online,
      pl: p.pl || '',
      lv: levelOfPlayer(p),
      pet: p.acct && p.acct.items ? p.acct.items.pet : '',
      drawing: room.phase === 'round' && room.drawer === p.key,
      guessed: room.phase === 'round' && p.guessed
    };
  });
}

function sendPlayers() { io.emit('players', publicPlayers()); }
function sys(text, kind) { io.emit('chat', { k: kind || 'sys', text: text }); }

function computeAwards() {
  const ps = room.players;
  const out = [];
  function pick(id, title, score, detail) {
    let w = null, v = null;
    ps.forEach(function (p) {
      const x = score(p);
      if (x === null || x === undefined) return;
      if (v === null || x > v) { v = x; w = p; }
    });
    if (w) out.push({ id: id, title: title, nick: w.nick, av: w.av || '', detail: detail(v, w) });
  }
  pick('fast', 'RÁPIDO NO GATILHO', function (p) { return p.stats.fast === null ? null : -p.stats.fast; }, function (v) { return 'acertou em ' + (-v).toFixed(1).replace('.', ',') + ' s'; });
  pick('artist', 'MELHOR ARTISTA', function (p) { return p.stats.drawnHits >= 1 ? p.stats.drawnHits : null; }, function (v) { return v + (v === 1 ? ' acerto' : ' acertos') + ' nos seus desenhos'; });
  pick('guesser', 'MESTRE DOS PALPITES', function (p) { return p.stats.hits >= 1 ? p.stats.hits : null; }, function (v) { return v + (v === 1 ? ' palavra' : ' palavras') + ' adivinhadas'; });
  pick('loved', 'MAIS APLAUDIDO', function (p) { return p.stats.reacts >= 2 ? p.stats.reacts : null; }, function (v) { return v + ' reações nos desenhos'; });
  pick('mystery', 'DESENHO MISTERIOSO', function (p) { return p.stats.mystery >= 1 ? p.stats.mystery : null; }, function (v) { return 'ninguém adivinhou ' + (v === 1 ? 'um desenho' : v + ' desenhos'); });
  pick('chute', 'CHUTADOR', function (p) { return p.stats.misses >= 4 ? p.stats.misses : null; }, function (v) { return v + ' palpites errados'; });
  return out;
}

function ranking() {
  return room.players
    .map(function (p, i) { return { nick: p.nick, score: p.score, i: i }; })
    .sort(function (a, b) { return b.score - a.score || a.i - b.i; })
    .map(function (r) { return { nick: r.nick, score: r.score }; });
}

/* ---------- palavra, máscara e dicas ---------- */

function isLetter(ch) { return /[\p{L}\p{N}]/u.test(ch); }

function makeMask() {
  let out = '';
  const chars = Array.from(room.word);
  for (let i = 0; i < chars.length; i++) {
    out += isLetter(chars[i]) && !room.revealed.has(i) ? '_' : chars[i];
  }
  return out;
}

function maybeReveal() {
  const total = room.cfg.seconds * 1000;
  const frac = (room.endAt - Date.now()) / total;
  const chars = Array.from(room.word);
  const idx = [];
  chars.forEach(function (c, i) { if (isLetter(c)) idx.push(i); });
  const maxRev = Math.max(1, Math.floor(idx.length / 3));
  let want = 0;
  if (frac <= 0.6) want = 1;
  if (frac <= 0.35) want = 2;
  want = Math.min(want, maxRev);
  let changed = false;
  while (room.revealed.size < want) {
    const left = idx.filter(function (i) { return !room.revealed.has(i); });
    if (!left.length) break;
    room.revealed.add(left[Math.floor(Math.random() * left.length)]);
    changed = true;
  }
  if (changed) {
    room.mask = makeMask();
    room.players.forEach(function (p) {
      if (p.id && p.key !== room.drawer && !p.guessed) io.to(p.id).emit('hint', { mask: room.mask });
    });
  }
}

/* ---------- fluxo da partida ---------- */

function roundPayload() {
  return {
    n: room.n,
    total: room.cfg.total,
    seconds: room.cfg.seconds,
    drawer: (playerByKey(room.drawer) || {}).nick || '',
    mask: room.mask,
    left: Math.max(0, room.endAt - Date.now())
  };
}

function startGame(starter, data) {
  if (room.phase !== 'lobby') return;
  if (onlinePlayers().length < 2) {
    starter.emit('chat', { k: 'warn', text: 'É preciso pelo menos 2 pessoas na sala.' });
    return;
  }
  const d = data || {};
  const words = [];
  const seen = new Set();
  (Array.isArray(d.words) ? d.words : []).slice(0, 4000).forEach(function (w) {
    const t = String(w || '').replace(/\s+/g, ' ').trim();
    if (t.length < 2 || t.length > 40) return;
    const k = norm(t);
    if (!k || seen.has(k)) return;
    seen.add(k);
    words.push(t);
  });
  if (words.length < 5) {
    starter.emit('chat', { k: 'warn', text: 'O tema precisa de pelo menos 5 palavras.' });
    return;
  }
  const total = Math.max(1, Math.min(30, Math.floor(Number(d.rounds) || 5)));
  const seconds = Math.max(20, Math.min(300, Math.floor(Number(d.seconds) || 60)));
  room.cfg = {
    key: String(d.key || '').slice(0, 40),
    nome: String(d.nome || 'Tema').slice(0, 40),
    total: total,
    seconds: seconds,
    words: words
  };
  room.bag = shuffle(words.slice());
  room.n = 0;
  room.turn = -1;
  room.order = shuffle(onlinePlayers().map(function (p) { return p.key; }));
  room.players.forEach(function (p) { p.score = 0; p.gain = 0; p.guessed = false; p.stats = newStats(); });
  endAllDuos();
  io.emit('game_start', { key: room.cfg.key, nome: room.cfg.nome, total: total, seconds: seconds, by: playerOf(starter).nick });
  sys('Partida iniciada: ' + room.cfg.nome + ', ' + total + ' rodadas de ' + seconds + 's.');
  startRound();
}

function nextDrawer() {
  for (let tries = 0; tries < room.order.length; tries++) {
    room.turn = (room.turn + 1) % room.order.length;
    const p = playerByKey(room.order[room.turn]);
    if (p && p.online) return p;
  }
  return null;
}

function startRound() {
  clearTimers();
  if (onlinePlayers().length < 2) { abortGame('few'); return; }
  const p = nextDrawer();
  if (!p) { abortGame('few'); return; }
  room.n++;
  if (!room.bag.length) room.bag = shuffle(room.cfg.words.slice());
  room.word = room.bag.pop();
  room.revealed = new Set();
  room.mask = makeMask();
  room.actions = [];
  room.cur = null;
  room.drawer = p.key;
  room.phase = 'round';
  room.players.forEach(function (q) { q.guessed = false; q.gain = 0; });
  room.endAt = Date.now() + room.cfg.seconds * 1000;
  io.emit('round', roundPayload());
  if (p.id) io.to(p.id).emit('word', { word: room.word });
  sys('Rodada ' + room.n + '/' + room.cfg.total + ': ' + p.nick + ' vai desenhar.');
  sendPlayers();
  room.timer = setInterval(tickRound, 500);
}

function tickRound() {
  if (room.phase !== 'round') return;
  if (Date.now() >= room.endAt) { endRound('time'); return; }
  maybeReveal();
}

function everyoneGuessed() {
  const guessers = onlinePlayers().filter(function (p) { return p.key !== room.drawer; });
  return guessers.length > 0 && guessers.every(function (p) { return p.guessed; });
}

function endRound(reason) {
  if (room.phase !== 'round') return;
  clearTimers();
  room.phase = 'between';
  commitCur();
  const last = room.n >= room.cfg.total;
  const drawer = playerByKey(room.drawer);
  if (drawer && reason === 'time' && !room.players.some(function (q) { return q.guessed; })) drawer.stats.mystery++;
  const gains = room.players
    .filter(function (p) { return p.gain > 0; })
    .sort(function (a, b) { return b.gain - a.gain; })
    .map(function (p) { return { nick: p.nick, gain: p.gain }; });
  io.emit('round_end', {
    word: room.word,
    reason: reason,
    last: last,
    nextIn: last ? 0 : BETWEEN_S,
    drawer: drawer ? drawer.nick : '',
    gains: gains,
    actions: room.actions,
    awards: last ? computeAwards() : null,
    ranking: last ? ranking() : null
  });
  sendPlayers();
  if (last) {
    try { garticRewards(); } catch (e) { console.error('recompensas gartic', e); }
    room.phase = 'lobby';
    room.drawer = null;
    sendPlayers();
  } else {
    room.nextTimer = setTimeout(startRound, BETWEEN_S * 1000);
  }
}

function abortGame(reason) {
  const wasRunning = room.phase !== 'lobby';
  clearTimers();
  if (wasRunning) {
    io.emit('round_end', { word: '', reason: reason, last: true, nextIn: 0, drawer: '', gains: [], ranking: ranking() });
  }
  room.phase = 'lobby';
  room.drawer = null;
  room.cur = null;
  room.actions = [];
  sendPlayers();
}

function correctGuess(p) {
  p.guessed = true;
  const left = Math.max(0, (room.endAt - Date.now()) / 1000);
  const took = Math.max(0, room.cfg.seconds - left);
  p.stats.hits++;
  if (p.stats.fast === null || took < p.stats.fast) p.stats.fast = took;
  const pts = 100 + Math.round(400 * left / room.cfg.seconds);
  p.score += pts;
  p.gain += pts;
  const d = playerByKey(room.drawer);
  if (d) {
    d.stats.drawnHits++;
    const dp = Math.round(pts / 4);
    d.score += dp;
    d.gain += dp;
  }
  sys(p.nick + ' acertou! (+' + pts + ')', 'ok');
  if (p.id) io.to(p.id).emit('word', { word: room.word });
  sendPlayers();
  if (everyoneGuessed()) endRound('all');
}

/* ---------- entrada e saída de jogadores ---------- */

function sendStateTo(socket, p) {
  if (room.phase === 'lobby' || !room.cfg) return;
  socket.emit('game_start', { key: room.cfg.key, nome: room.cfg.nome, total: room.cfg.total, seconds: room.cfg.seconds, by: '' });
  if (room.phase === 'round') {
    socket.emit('round', roundPayload());
    socket.emit('snapshot', { actions: room.actions, cur: room.cur });
    if (p.key === room.drawer || p.guessed) socket.emit('word', { word: room.word });
  }
  if (room.order.indexOf(p.key) === -1) room.order.push(p.key);
}

function removePlayer(p) {
  if (p.offTimer) { clearTimeout(p.offTimer); p.offTimer = null; }
  const idx = room.players.indexOf(p);
  if (idx === -1) return;
  duoLeave(p);
  saveAcct(p, true);
  room.players.splice(idx, 1);
  sys(p.nick + ' saiu.');
  if (room.phase === 'round' && p.key === room.drawer) endRound('drawer_left');
  else if (room.phase === 'round' && everyoneGuessed()) endRound('all');
  if (room.phase !== 'lobby' && onlinePlayers().length < 2) abortGame('few');
  if (!room.players.length) resetRoom();
  sendPlayers();
}

/* ---------- desenho ---------- */

const HEX = /^#[0-9a-fA-F]{6}$/;
function num(v, lo, hi) { v = Number(v); if (!isFinite(v)) v = 0; return Math.max(lo, Math.min(hi, v)); }
function nums(arr, cap) {
  const out = [];
  if (!Array.isArray(arr)) return out;
  for (let i = 0; i < arr.length && i < cap; i++) {
    const v = Number(arr[i]);
    if (isFinite(v)) out.push(Math.max(-10, Math.min(2000, v)));
  }
  return out;
}

function cleanAction(a) {
  if (!a || typeof a !== 'object') return null;
  const c = HEX.test(a.c) ? a.c : '#232323';
  if (a.t === 'stroke') return { t: 'stroke', c: c, w: num(a.w, 1, 60), n: num(a.n, 1, 20), px: !!a.px, p: nums(a.p, 40000) };
  if (a.t === 'spray') return { t: 'spray', c: c, r: num(a.r, 1, 60), px: !!a.px, p: nums(a.p, 40000) };
  if (a.t === 'shape') {
    const k = a.k === 'rect' || a.k === 'oval' ? a.k : 'line';
    const pts = nums(a.a, 4);
    while (pts.length < 4) pts.push(0);
    return { t: 'shape', k: k, c: c, w: num(a.w, 1, 60), n: num(a.n, 1, 20), px: !!a.px, f: !!a.f, a: pts };
  }
  if (a.t === 'fill') return { t: 'fill', c: c, x: num(a.x, 0, 2000), y: num(a.y, 0, 2000) };
  if (a.t === 'clear') return { t: 'clear' };
  return null;
}

function commitCur() {
  if (room.cur) {
    if (room.actions.length < 4000) room.actions.push(room.cur);
    room.cur = null;
  }
}

function handleDraw(socket, m) {
  if (!m || typeof m !== 'object') return;
  switch (m.k) {
    case 'begin': {
      const a = cleanAction(m.a);
      if (!a || a.t === 'fill' || a.t === 'clear') return;
      commitCur();
      room.cur = a;
      socket.broadcast.emit('draw', { k: 'begin', a: a });
      break;
    }
    case 'pts': {
      if (!room.cur || (room.cur.t !== 'stroke' && room.cur.t !== 'spray')) return;
      const p = nums(m.p, 4000);
      if (!p.length || room.cur.p.length > 40000) return;
      for (let i = 0; i < p.length; i++) room.cur.p.push(p[i]);
      socket.broadcast.emit('draw', { k: 'pts', p: p });
      break;
    }
    case 'shape': {
      if (!room.cur || room.cur.t !== 'shape') return;
      const a = nums(m.a, 4);
      if (a.length !== 4) return;
      room.cur.a = a;
      socket.broadcast.emit('draw', { k: 'shape', a: a });
      break;
    }
    case 'end':
      commitCur();
      socket.broadcast.emit('draw', { k: 'end' });
      break;
    case 'act': {
      const a = cleanAction(m.a);
      if (!a || (a.t !== 'fill' && a.t !== 'clear')) return;
      commitCur();
      if (room.actions.length < 4000) room.actions.push(a);
      socket.broadcast.emit('draw', { k: 'act', a: a });
      break;
    }
    case 'undo':
      commitCur();
      room.actions.pop();
      socket.broadcast.emit('draw', { k: 'undo' });
      break;
    default:
  }
}

/* ---------- servidor ---------- */

/* ====================================================================
   PERSISTÊNCIA, CONTAS, MOEDAS, NÍVEIS, CONQUISTAS E RANKING
   ==================================================================== */

const SB_URL = String(process.env.SUPABASE_URL || '').trim().replace(/\/+$/, '');
const SB_KEY = String(process.env.SUPABASE_KEY || '').trim();
const ADMIN_KEY = String(process.env.ADMIN_KEY || '').trim();
const DATA_FILE = process.env.DATA_FILE || path.join(__dirname, 'data.json');

/* ---------- banco: Supabase (se configurado) ou arquivo local ---------- */
function supabaseStore() {
  async function sb(method, pathq, body, extra) {
    const res = await fetch(SB_URL + '/rest/v1/' + pathq, {
      method: method,
      headers: Object.assign({ apikey: SB_KEY, 'Content-Type': 'application/json' }, SB_KEY.indexOf('sb_') === 0 ? {} : { Authorization: 'Bearer ' + SB_KEY }, extra || {}),
      body: body === undefined ? undefined : JSON.stringify(body)
    });
    const t = await res.text();
    if (!res.ok) throw new Error('supabase ' + res.status + ' ' + t.slice(0, 200));
    return t ? JSON.parse(t) : null;
  }
  const enc = encodeURIComponent;
  return {
    kind: 'supabase',
    async listPlayers() { return (await sb('GET', 'players?select=key,nick,av,xp,items&order=xp.desc&limit=200')) || []; },
    async galList(n) { return (await sb('GET', 'gallery?select=id,key,nick,word,theme,img,likes,n_likes,created_at&order=created_at.desc&limit=' + n)) || []; },
    async galAdd(row) { const r = await sb('POST', 'gallery', row, { Prefer: 'return=representation' }); return r && r[0] ? r[0] : null; },
    async galGet(id) { id = parseInt(id, 10); if (!(id > 0)) return null; const r = await sb('GET', 'gallery?id=eq.' + id + '&select=id,key,nick,likes,n_likes'); return r && r[0] ? r[0] : null; },
    async galSet(id, patch) { await sb('PATCH', 'gallery?id=eq.' + parseInt(id, 10), patch, { Prefer: 'return=minimal' }); },
    async galDel(id) { await sb('DELETE', 'gallery?id=eq.' + parseInt(id, 10), undefined, { Prefer: 'return=minimal' }); },
    async getPlayer(key) { const r = await sb('GET', 'players?key=eq.' + enc(key) + '&select=*'); return r && r[0] ? r[0] : null; },
    async createPlayer(row) { await sb('POST', 'players', row, { Prefer: 'return=minimal' }); },
    async savePlayer(key, patch) { await sb('PATCH', 'players?key=eq.' + enc(key), Object.assign({ updated_at: new Date().toISOString() }, patch), { Prefer: 'return=minimal' }); },
    async putScore(game, period, key, nick, score) {
      await sb('POST', 'scores?on_conflict=game,period,key', { game: game, period: period, key: key, nick: nick, score: score, updated_at: new Date().toISOString() }, { Prefer: 'resolution=merge-duplicates,return=minimal' });
    },
    async top(game, period, n) { return (await sb('GET', 'scores?game=eq.' + enc(game) + '&period=eq.' + enc(period) + '&select=nick,score&order=score.desc&limit=' + n)) || []; }
  };
}

function fileStore() {
  let db = { players: {}, scores: {}, gallery: [], gseq: 0 };
  try { db = Object.assign(db, JSON.parse(fs.readFileSync(DATA_FILE, 'utf8'))); } catch (e) { /* começa vazio */ }
  let timer = null;
  function flush() {
    timer = null;
    try { fs.writeFileSync(DATA_FILE, JSON.stringify(db)); } catch (e) { console.error('arquivo de dados', e.message); }
  }
  function later() { if (!timer) { timer = setTimeout(flush, 1500); if (timer.unref) timer.unref(); } }
  const clone = function (o) { return o ? JSON.parse(JSON.stringify(o)) : null; };
  return {
    kind: 'arquivo',
    flush: flush,
    async listPlayers() { return Object.keys(db.players).map(function (k) { const r = db.players[k]; return { key: r.key, nick: r.nick, av: r.av, xp: r.xp, items: r.items }; }); },
    async galList(n) { return db.gallery.slice().sort(function (a, b) { return b.id - a.id; }).slice(0, n).map(clone); },
    async galAdd(row) { const r = Object.assign({ id: ++db.gseq, created_at: new Date().toISOString() }, clone(row)); db.gallery.push(r); later(); return clone(r); },
    async galGet(id) { id = parseInt(id, 10); return clone(db.gallery.find(function (r) { return r.id === id; })); },
    async galSet(id, patch) { id = parseInt(id, 10); const r = db.gallery.find(function (x) { return x.id === id; }); if (r) Object.assign(r, clone(patch)); later(); },
    async galDel(id) { id = parseInt(id, 10); db.gallery = db.gallery.filter(function (r) { return r.id !== id; }); later(); },
    async getPlayer(key) { return clone(db.players[key]); },
    async createPlayer(row) { db.players[row.key] = clone(row); later(); },
    async savePlayer(key, patch) { if (db.players[key]) Object.assign(db.players[key], clone(patch)); later(); },
    async putScore(game, period, key, nick, score) { db.scores[game + '|' + period + '|' + key] = { game: game, period: period, key: key, nick: nick, score: score }; later(); },
    async top(game, period, n) {
      return Object.keys(db.scores).map(function (k) { return db.scores[k]; })
        .filter(function (r) { return r.game === game && r.period === period; })
        .sort(function (a, b) { return b.score - a.score; }).slice(0, n)
        .map(function (r) { return { nick: r.nick, score: r.score }; });
    }
  };
}
const Store = SB_URL && SB_KEY ? supabaseStore() : fileStore();

/* ---------- PIN ---------- */
function scryptAsync(pin, salt) {
  return new Promise(function (resolve, reject) { crypto.scrypt(pin, salt, 32, function (e, k) { if (e) reject(e); else resolve(k.toString('hex')); }); });
}
async function hashPin(pin, salt) { return scryptAsync(String(pin), salt); }
async function checkPin(pin, acct) {
  const h = await scryptAsync(String(pin), acct.salt);
  const a = Buffer.from(h, 'hex'), b = Buffer.from(String(acct.hash), 'hex');
  return a.length === b.length && crypto.timingSafeEqual(a, b);
}
const fails = {};   // chave -> { n, until }

/* ---------- níveis e títulos ---------- */
function lvOf(xp) { return Math.max(1, Math.floor((1 + Math.sqrt(1 + Math.max(0, xp) / 12.5)) / 2)); }
function xpAt(l) { return 50 * l * (l - 1); }
const TITLES = [[1, 'Novato do Fliperama'], [3, 'Ficha Quente'], [5, 'Craque do Joystick'], [8, 'Mestre dos Pixels'], [12, 'Lenda do Salão'], [16, 'Rei do Fliperama'], [20, 'Imortal do Arcade']];
function titleOf(l) { let t = TITLES[0][1]; TITLES.forEach(function (r) { if (l >= r[0]) t = r[1]; }); return t; }

/* ---------- datas (horário de Brasília) ---------- */
function nowMs() { return process.env.FAKE_NOW ? Date.parse(process.env.FAKE_NOW) : Date.now(); }
function brt() { return new Date(nowMs() - 3 * 3600 * 1000); }
function dayKey(d) { d = d || brt(); return d.toISOString().slice(0, 10); }
function weekKey() {
  const d = brt();
  const t = new Date(Date.UTC(d.getUTCFullYear(), d.getUTCMonth(), d.getUTCDate()));
  const dow = t.getUTCDay() || 7;
  t.setUTCDate(t.getUTCDate() + 4 - dow);
  const y0 = new Date(Date.UTC(t.getUTCFullYear(), 0, 1));
  return t.getUTCFullYear() + '-W' + String(Math.ceil(((t - y0) / 86400000 + 1) / 7)).padStart(2, '0');
}
function yesterdayKey() { return dayKey(new Date(brt().getTime() - 86400000)); }

/* ---------- conquistas ---------- */
const MASTER = { pinball: 100000, breakout: 1500, cobrinha: 500, invasores: 2500, blocos: 3000, asteroides: 3000, corrida: 3000, memoria: 1500 };
const GNAME = { pinball: 'Pinball', breakout: 'Blocos', cobrinha: 'Cobrinha', invasores: 'Invasores', blocos: 'Tetris', asteroides: 'Asteroides', corrida: 'Corrida', memoria: 'Memória' };
const ACH = [
  { id: 'ficha', n: 'Primeira Ficha', d: 'Jogue qualquer máquina solo.', c: 10, t: function (s) { return s.runs >= 1; } },
  { id: 'salao', n: 'Rodou o Salão', d: 'Jogue as 8 máquinas solo.', c: 40, t: function (s) { return Object.keys(s.solo).length >= 8; } },
  { id: 'viciado', n: 'Viciado', d: 'Jogue 25 partidas solo.', c: 30, t: function (s) { return s.runs >= 25; } },
  { id: 'maratona', n: 'Maratonista', d: 'Jogue 100 partidas solo.', c: 100, t: function (s) { return s.runs >= 100; } }
].concat(Object.keys(MASTER).map(function (g) {
  return { id: 'mestre_' + g, n: 'Mestre: ' + GNAME[g], d: 'Faça ' + MASTER[g].toLocaleString('pt-BR') + ' pontos em ' + GNAME[g] + '.', c: 30, t: function (s) { return s.solo[g] && s.solo[g].best >= MASTER[g]; } };
})).concat([
  { id: 'top3', n: 'No Placar', d: 'Entre no top 3 de uma máquina.', c: 25, t: function (s) { return s.top3 >= 1; } },
  { id: 'top1', n: 'Dono do Placar', d: 'Fique em 1º lugar de uma máquina.', c: 50, t: function (s) { return s.top1 >= 1; } },
  { id: 'rival', n: 'Primeira Vitória', d: 'Vença uma pessoa numa máquina de dupla.', c: 25, t: function (s) { return s.duoW >= 1; } },
  { id: 'chamas', n: 'Em Chamas', d: 'Vença 3 duelos seguidos.', c: 40, t: function (s) { return s.duoBest >= 3; } },
  { id: 'duelista', n: 'Duelista', d: 'Vença 10 duelos.', c: 60, t: function (s) { return s.duoW >= 10; } },
  { id: 'quatro', n: 'Quatro Estilos', d: 'Vença nos 4 jogos de dupla.', c: 60, t: function (s) { return Object.keys(s.duoWon).length >= 4; } },
  { id: 'gartic1', n: 'Rabisqueiro', d: 'Jogue uma partida de Gartic.', c: 10, t: function (s) { return s.g.games >= 1; } },
  { id: 'acerto10', n: 'Olho Clínico', d: 'Acerte 10 palpites.', c: 25, t: function (s) { return s.g.hits >= 10; } },
  { id: 'acerto50', n: 'Vidente', d: 'Acerte 50 palpites.', c: 60, t: function (s) { return s.g.hits >= 50; } },
  { id: 'artista', n: 'Artista', d: 'Faça 3 pessoas acertarem o seu desenho numa partida.', c: 30, t: function (s) { return s.g.bestDrawn >= 3; } },
  { id: 'relampago', n: 'Relâmpago', d: 'Acerte um palpite em menos de 5 segundos.', c: 30, t: function (s) { return s.g.fastest !== null && s.g.fastest < 5; } },
  { id: 'rei_g', n: 'Rei do Rabisco', d: 'Vença uma partida de Gartic.', c: 40, t: function (s) { return s.g.wins >= 1; } },
  { id: 'rei_g5', n: 'Pentacampeão', d: 'Vença 5 partidas de Gartic.', c: 80, t: function (s) { return s.g.wins >= 5; } },
  { id: 'dia3', n: 'De Casa', d: 'Entre no salão 3 dias seguidos.', c: 30, t: function (s, a) { return a.streak >= 3; } },
  { id: 'dia7', n: 'Morador', d: 'Entre no salão 7 dias seguidos.', c: 80, t: function (s, a) { return a.streak >= 7; } },
  { id: 'lv5', n: 'Nível 5', d: 'Chegue ao nível 5.', c: 30, t: function (s, a) { return lvOf(a.xp) >= 5; } },
  { id: 'lv10', n: 'Nível 10', d: 'Chegue ao nível 10.', c: 100, t: function (s, a) { return lvOf(a.xp) >= 10; } },
  { id: 'rico', n: 'Cofrinho', d: 'Junte 500 moedas ao todo.', c: 50, t: function (s, a) { return a.total_coins >= 500; } }
]);
ACH.push(
  { id: 'comprador', n: 'Primeira Compra', d: 'Compre algo na loja.', c: 10, t: function (s, a) { return Object.keys(a.items.own).length >= 1; } },
  { id: 'colecionador', n: 'Colecionador', d: 'Tenha 10 itens diferentes.', c: 40, t: function (s, a) { return Object.keys(a.items.own).length >= 10; } },
  { id: 'decorador', n: 'Decorador', d: 'Coloque 8 itens no seu quarto.', c: 40, t: function (s, a) { return a.items.room.put.length >= 8; } },
  { id: 'adotou', n: 'Pai de Pet', d: 'Adote um bichinho.', c: 20, t: function (s, a) { return !!a.items.pet; } },
  { id: 'visitante', n: 'Vizinho Simpático', d: 'Visite 5 quartos de outras pessoas.', c: 30, t: function (s, a) { return Object.keys(a.items.visits).length >= 5; } },
  { id: 'galerista', n: 'Na Galeria', d: 'Publique um desenho na galeria.', c: 20, t: function (s, a) { return a.items.gal.total >= 1; } },
  { id: 'estrela', n: 'Artista Querido', d: 'Receba 10 curtidas nos seus desenhos.', c: 50, t: function (s, a) { return a.items.gal.likes >= 10; } },
  { id: 'popular', n: 'Quarto Popular', d: 'Receba 5 curtidas no seu quarto.', c: 40, t: function (s, a) { return Object.keys(a.items.likes).length >= 5; } }
);
const ACH_PUB = ACH.map(function (a) { return { id: a.id, n: a.n, d: a.d, c: a.c }; });

/* ---------- conta na memória ---------- */
function newAcctStats() {
  return { runs: 0, solo: {}, duoW: 0, duoL: 0, duoD: 0, duoStreak: 0, duoBest: 0, duoWon: {}, top3: 0, top1: 0,
    g: { games: 0, hits: 0, wins: 0, drawn: 0, fastest: null, bestScore: 0, bestDrawn: 0 }, dayCoins: { d: '', n: 0 }, wk: { w: '', best: {} } };
}
function normalizeAcct(a) {
  const base = newAcctStats();
  const s = a.stats && typeof a.stats === 'object' ? a.stats : {};
  a.stats = Object.assign(base, s);
  a.stats.g = Object.assign(base.g, s.g || {});
  a.stats.dayCoins = Object.assign({ d: '', n: 0 }, s.dayCoins || {});
  a.stats.wk = Object.assign({ w: '', best: {} }, s.wk || {});
  a.ach = a.ach && typeof a.ach === 'object' ? a.ach : {};
  normItems(a);
  a.coins = a.coins | 0; a.xp = a.xp | 0; a.total_coins = a.total_coins | 0; a.streak = a.streak | 0;
  a.last_daily = a.last_daily || '';
  return a;
}
function acctPayload(p) {
  const a = p.acct, l = lvOf(a.xp), solo = {};
  Object.keys(a.stats.solo).forEach(function (g) { solo[g] = { n: a.stats.solo[g].n, best: a.stats.solo[g].best }; });
  return { nick: p.nick, coins: a.coins, xp: a.xp, lv: l, lo: xpAt(l), hi: xpAt(l + 1), title: titleOf(l), ach: Object.keys(a.ach), streak: a.streak,
    items: itemsPub(a), stats: { runs: a.stats.runs, solo: solo, duoW: a.stats.duoW, duoL: a.stats.duoL, duoD: a.stats.duoD, g: a.stats.g } };
}
function levelOfPlayer(p) { return p.acct ? lvOf(p.acct.xp) : 1; }

/* salva com atraso para não sobrecarregar o banco */
function saveAcct(p, now) {
  if (!p.acct) return;
  p.acctDirty = true;
  if (p.saveTimer && !now) return;
  if (p.saveTimer) { clearTimeout(p.saveTimer); p.saveTimer = null; }
  const run = function () {
    p.saveTimer = null;
    if (!p.acctDirty || !p.acct) return Promise.resolve();
    p.acctDirty = false;
    const a = p.acct;
    return Store.savePlayer(p.key, { nick: p.nick, av: a.av || '', coins: a.coins, xp: a.xp, total_coins: a.total_coins, ach: a.ach, stats: a.stats, items: a.items, last_daily: a.last_daily, streak: a.streak })
      .catch(function (e) { console.error('salvar conta', e.message); p.acctDirty = true; p.saveTimer = setTimeout(run, 10000); });
  };
  if (now) return run();
  p.saveTimer = setTimeout(run, 3000);
}

/* ---------- recompensas ---------- */
function grant(p, r) {
  // r: { kind, coins, xp, ...extras }  devolve o que foi dado e envia ao jogador
  const a = p.acct;
  if (!a) return null;
  const lv0 = lvOf(a.xp);
  const out = { kind: r.kind, coins: Math.max(0, r.coins | 0), xp: Math.max(0, r.xp | 0), ach: [], lvUp: 0 };
  Object.keys(r).forEach(function (k) { if (['coins', 'xp'].indexOf(k) === -1) out[k] = r[k]; });
  a.coins += out.coins; a.total_coins += out.coins; a.xp += out.xp;
  // conquistas (podem render moedas e liberar outras)
  for (let guard = 0; guard < 6; guard++) {
    let found = false;
    ACH.forEach(function (d) {
      if (a.ach[d.id]) return;
      let ok = false;
      try { ok = !!d.t(a.stats, a); } catch (e) { ok = false; }
      if (!ok) return;
      a.ach[d.id] = Date.now();
      a.coins += d.c; a.total_coins += d.c; a.xp += 40;
      out.coins += d.c; out.xp += 40;
      out.ach.push({ id: d.id, n: d.n, c: d.c });
      found = true;
    });
    if (!found) break;
  }
  const lv1 = lvOf(a.xp);
  if (lv1 > lv0) {
    const bonus = 5 * (lv1 - lv0);
    a.coins += bonus; a.total_coins += bonus; out.coins += bonus;
    out.lvUp = lv1; out.title = titleOf(lv1);
  }
  saveAcct(p);
  if (p.id) {
    io.to(p.id).emit('reward', out);
    io.to(p.id).emit('account', acctPayload(p));
  }
  if (out.lvUp) sendPlayers();
  return out;
}

function dailyBonus(p) {
  const a = p.acct, today = dayKey();
  if (a.last_daily === today) return;
  a.streak = a.last_daily === yesterdayKey() ? a.streak + 1 : 1;
  a.last_daily = today;
  grant(p, { kind: 'daily', coins: 10 + 2 * Math.min(a.streak, 7), xp: 20, streak: a.streak });
}

/* ---------- ranking ---------- */
const topCache = {};
function invalidateTop(game) { Object.keys(topCache).forEach(function (k) { if (k.indexOf(game + '|') === 0) delete topCache[k]; }); }
async function getTop(game, period) {
  const k = game + '|' + period, c = topCache[k];
  if (c && Date.now() - c.t < 15000) return c.v;
  const v = await Store.top(game, period, 10);
  topCache[k] = { t: Date.now(), v: v };
  return v;
}
const TOP_GAMES = new Set(['pinball', 'breakout', 'cobrinha', 'invasores', 'blocos', 'asteroides', 'corrida', 'memoria', 'gartic']);

// registra pontuação nas listas geral e da semana; devolve { rec, rank }
async function submitScore(p, game, score) {
  const a = p.acct, s = a.stats, wk = weekKey();
  if (s.wk.w !== wk) s.wk = { w: wk, best: {} };
  let rec = false, improved = false;
  const prev = s.solo[game] ? s.solo[game].best : (game === 'gartic' ? s.g.bestScore : 0);
  if (score > prev) {
    improved = true;
    rec = prev > 0;
    await Store.putScore(game, 'all', p.key, p.nick, score);
    invalidateTop(game);
  }
  if (score > (s.wk.best[game] || 0)) {
    s.wk.best[game] = score;
    await Store.putScore(game, wk, p.key, p.nick, score);
    invalidateTop(game);
  }
  let rank = 0;
  try {
    const list = await getTop(game, 'all');
    const i = list.findIndex(function (r) { return r.nick === p.nick; });
    rank = i >= 0 ? i + 1 : 0;
  } catch (e) { /* sem rank */ }
  return { rec: rec, improved: improved, rank: rank };
}

/* ---------- fliperama solo ---------- */
const DIV = { pinball: 5000, breakout: 100, cobrinha: 40, invasores: 150, blocos: 200, asteroides: 150, corrida: 150, memoria: 100 };
const SCORE_CAP = { pinball: 5000000, breakout: 200000, cobrinha: 200000, invasores: 200000, blocos: 500000, asteroides: 200000, corrida: 500000, memoria: 100000 };
const RUN_COIN_CAP = 20, DAY_COIN_CAP = 150;

async function handleRun(p, m) {
  if (!p || !p.acct || !m) return;
  const game = String(m.game || '');
  if (!SOLO_IDS.has(game)) return;
  const now = Date.now();
  if (p.lastRun && now - p.lastRun < 6000) return;
  const secs = Math.max(0, Math.min(3600, Number(m.secs) || 0));
  if (secs < 5) return;
  p.lastRun = now;
  const score = Math.floor(Math.max(0, Math.min(SCORE_CAP[game], Number(m.score) || 0)));
  const a = p.acct, s = a.stats, today = dayKey();
  s.runs++;
  const g = s.solo[game] || (s.solo[game] = { n: 0, best: 0 });
  g.n++;
  const sc = await submitScore(p, game, score);
  if (score > g.best) g.best = score;
  if (sc.rank >= 1 && sc.rank <= 3 && sc.improved) { s.top3++; if (sc.rank === 1) s.top1++; }
  if (s.dayCoins.d !== today) s.dayCoins = { d: today, n: 0 };
  let coins = Math.min(RUN_COIN_CAP, (score > 0 ? 1 : 0) + Math.floor(score / DIV[game]));
  coins = Math.max(0, Math.min(coins, DAY_COIN_CAP - s.dayCoins.n));
  s.dayCoins.n += coins;
  const mu = evMult();
  coins = boosted(coins);
  grant(p, { kind: 'run', game: game, score: score, rec: sc.rec, rank: sc.rank, mult: mu, coins: coins, xp: coins > 0 ? 5 + coins * 2 : 2 });
}

/* ---------- duelos ---------- */
function settleDuo(p, q) {
  // p e q reportaram; confere se os resultados batem
  const ra = p.pend.res, rb = q.pend.res, game = p.pend.game || q.pend.game || '';
  const ok = (ra === 'win' && rb === 'loss') || (ra === 'loss' && rb === 'win') || (ra === 'draw' && rb === 'draw');
  [p, q].forEach(function (x) { if (x.pendTimer) { clearTimeout(x.pendTimer); x.pendTimer = null; } });
  [[p, ra], [q, rb]].forEach(function (pair) {
    const x = pair[0], res = ok ? pair[1] : 'part', s = x.acct.stats;
    let coins = 3, xp = 8;
    if (res === 'win') { s.duoW++; s.duoStreak++; if (s.duoStreak > s.duoBest) s.duoBest = s.duoStreak; s.duoWon[game] = (s.duoWon[game] || 0) + 1; coins = 15; xp = 30; }
    else if (res === 'loss') { s.duoL++; s.duoStreak = 0; coins = 5; xp = 12; }
    else if (res === 'draw') { s.duoD++; coins = 8; xp = 18; }
    grant(x, { kind: 'duo', game: game, res: res, mult: evMult(), coins: boosted(coins), xp: xp });
  });
  p.pend = null; q.pend = null;
}
function handleDuoResult(p, m) {
  if (!p || !p.acct || !p.duoWith) return;
  const res = m && ['win', 'loss', 'draw'].indexOf(m.res) !== -1 ? m.res : '';
  if (!res) return;
  const now = Date.now();
  if (p.lastDuoRes && now - p.lastDuoRes < 10000) return;
  p.lastDuoRes = now;
  const q = playerByKey(p.duoWith);
  if (!q || !q.acct) return;
  p.pend = { res: res, game: p.duoGame || '', t: now, vs: q.key };
  if (q.pend && q.pend.vs === p.key && now - q.pend.t < 20000) { settleDuo(p, q); return; }
  const t = now;
  p.pendTimer = setTimeout(function () {
    p.pendTimer = null;
    if (p.pend && p.pend.t === t) { p.pend = null; grant(p, { kind: 'duo', game: p.duoGame || '', res: 'part', coins: 3, xp: 8 }); }
  }, 20000);
}

/* ---------- Gartic: recompensas no fim da partida ---------- */
function garticRewards() {
  const list = room.players.filter(function (p) { return p.acct; }).slice().sort(function (a, b) { return b.score - a.score; });
  if (!list.length) return;
  const top = list[0].score;
  list.forEach(function (p, i) {
    const s = p.acct.stats.g;
    const played = p.score > 0 || p.stats.hits > 0 || p.stats.drawnHits > 0;
    if (!played) return;
    s.games++; s.hits += p.stats.hits; s.drawn += p.stats.drawnHits;
    if (p.stats.drawnHits > s.bestDrawn) s.bestDrawn = p.stats.drawnHits;
    if (p.stats.fast !== null && (s.fastest === null || p.stats.fast < s.fastest)) s.fastest = p.stats.fast;
    const win = list.length >= 2 && p.score === top && top > 0;
    if (win) s.wins++;
    const coins = Math.min(30, Math.round(p.score / 60)) + (win ? 15 : 0);
    const xp = 20 + Math.min(80, Math.round(p.score / 20));
    const afterScore = function () {
      if (p.score > s.bestScore) s.bestScore = p.score;
      grant(p, { kind: 'gartic', score: p.score, win: win, rank: i + 1, mult: evMult(), coins: boosted(coins), xp: xp });
    };
    submitScore(p, 'gartic', p.score).then(function (r) { afterScore(); }, function (e) { console.error('placar gartic', e.message); afterScore(); });
  });
}


/* ====================================================================
   FASE 2: EVENTOS, LOJA, QUARTO E GALERIA
   ==================================================================== */

/* ---------- eventos e estações (horário de Brasília) ---------- */
function easterDate(y) {
  const a = y % 19, b = Math.floor(y / 100), c = y % 100, d = Math.floor(b / 4), e = b % 4, f = Math.floor((b + 8) / 25), g = Math.floor((b - f + 1) / 3);
  const h = (19 * a + b - d - g + 15) % 30, i = Math.floor(c / 4), k = c % 4, l = (32 + 2 * e + 2 * i - h - k) % 7, m = Math.floor((a + 11 * h + 22 * l) / 451);
  const month = Math.floor((h + l - 7 * m + 114) / 31), day = ((h + l - 7 * m + 114) % 31) + 1;
  return new Date(Date.UTC(y, month - 1, day));
}
function inMD(md, a, b) { return a <= b ? (md >= a && md <= b) : (md >= a || md <= b); }
// ev: { id, n, a, b (mês*100+dia) ou fn(hoje) -> bool, shopA, shopB, mult, sale }
const EVENTS = [
  { id: 'halloween', n: 'Halloween', a: 1020, b: 1103, shopA: 1010, shopB: 1107 },
  { id: 'blackfriday', n: 'Black Friday', a: 1123, b: 1130, sale: 0.25 },
  { id: 'natal', n: 'Natal', a: 1210, b: 1226, shopA: 1201, shopB: 1231 },
  { id: 'ano_novo', n: 'Ano Novo', a: 1227, b: 102, shopA: 1227, shopB: 110, mult: 2 },
  { id: 'junina', n: 'Festa Junina', a: 610, b: 705, shopA: 601, shopB: 710 },
  { id: 'carnaval', n: 'Carnaval', mult: 1.5, shopFrom: -60, shopTo: -44, fn: function (t, y) { const e = easterDate(y).getTime(); const d = Math.round((t - e) / 86400000); return d >= -51 && d <= -46; } },
  { id: 'pascoa', n: 'Páscoa', shopFrom: -21, shopTo: 1, fn: function (t, y) { const e = easterDate(y).getTime(); const d = Math.round((t - e) / 86400000); return d >= -7 && d <= 0; } }
];
function bdate() { const d = brt(); return new Date(Date.UTC(d.getUTCFullYear(), d.getUTCMonth(), d.getUTCDate())); }
function mdOf(d) { return (d.getUTCMonth() + 1) * 100 + d.getUTCDate(); }
function evActive(ev, shop) {
  const t = bdate(), y = t.getUTCFullYear(), md = mdOf(t);
  if (ev.fn) {
    if (!shop) return ev.fn(t.getTime(), y);
    const d = Math.round((t.getTime() - easterDate(y).getTime()) / 86400000);
    return d >= ev.shopFrom && d <= ev.shopTo;
  }
  return shop ? inMD(md, ev.shopA || ev.a, ev.shopB || ev.b) : inMD(md, ev.a, ev.b);
}
function isSextou() { const d = brt(); return d.getUTCDay() === 5 && d.getUTCHours() >= 17; }
function seasonOf() {
  const md = mdOf(bdate());
  if (inMD(md, 1221, 319)) return 'verao';
  if (inMD(md, 320, 620)) return 'outono';
  if (inMD(md, 621, 921)) return 'inverno';
  return 'primavera';
}
function activeEvents() { return EVENTS.filter(function (e) { return evActive(e, false); }); }
function evMult() {
  let m = 1;
  activeEvents().forEach(function (e) { if (e.mult && e.mult > m) m = e.mult; });
  if (isSextou() && m < 1.5) m = 1.5;
  return m;
}
function evSale() { let s = 0; activeEvents().forEach(function (e) { if (e.sale && e.sale > s) s = e.sale; }); return s; }
function eventsPayload() {
  const list = activeEvents().map(function (e) { return { id: e.id, n: e.n }; });
  if (isSextou()) list.push({ id: 'sextou', n: 'Sextou no Fliperama' });
  return { ev: list, mult: evMult(), sale: evSale(), season: seasonOf(), shop: EVENTS.filter(function (e) { return evActive(e, true); }).map(function (e) { return e.id; }) };
}

/* ---------- catálogo ---------- */
const CAT = [];
function I(id, n, cat, p, w, d, o) { CAT.push(Object.assign({ id: id, n: n, cat: cat, p: p, w: w || 1, d: d || 1 }, o || {})); }
// móveis (no chão)
I('sofa', 'Sofá retrô', 'movel', 90, 2, 1);
I('poltrona', 'Poltrona', 'movel', 60);
I('pufe', 'Pufe', 'movel', 30);
I('mesinha', 'Mesinha', 'movel', 35);
I('mesa', 'Mesa de jantar', 'movel', 80, 2, 1);
I('tv', 'TV de tubo', 'movel', 120);
I('computador', 'Computador 8-bit', 'movel', 140);
I('estante', 'Estante', 'movel', 70);
I('cama', 'Cama', 'movel', 110, 1, 2);
I('abajur', 'Abajur neon', 'movel', 35);
I('vaso', 'Planta em vaso', 'movel', 25);
I('caixa', 'Caixa de som', 'movel', 55);
I('geladeira', 'Frigobar', 'movel', 130);
I('aquario', 'Aquário', 'movel', 150);
I('fliper', 'Mini fliperama', 'movel', 220);
I('juke', 'Mini jukebox', 'movel', 260);
I('bau', 'Baú do tesouro', 'movel', 100);
I('trofeu', 'Troféu dourado', 'movel', 180);
// tapetes (planos)
I('tapete1', 'Tapete xadrez', 'tapete', 45, 2, 2, { flat: true });
I('tapete2', 'Tapete redondo', 'tapete', 60, 2, 2, { flat: true });
I('tapete3', 'Tapete neon', 'tapete', 90, 2, 2, { flat: true });
// quadros (na parede)
I('quadro1', 'Quadro Memphis', 'quadro', 30, 1, 1, { wall: true });
I('quadro2', 'Quadro Pôr do sol', 'quadro', 30, 1, 1, { wall: true });
I('quadro3', 'Quadro Pixel', 'quadro', 40, 1, 1, { wall: true });
I('relogio', 'Relógio de parede', 'quadro', 35, 1, 1, { wall: true });
I('neon', 'Letreiro neon', 'quadro', 70, 1, 1, { wall: true });
I('prateleira', 'Prateleira', 'quadro', 45, 1, 1, { wall: true });
I('espelho', 'Espelho', 'quadro', 40, 1, 1, { wall: true });
// sazonais
I('abobora', 'Abóbora esculpida', 'movel', 30, 1, 1, { ev: 'halloween' });
I('fantasma_d', 'Fantasma de lençol', 'movel', 35, 1, 1, { ev: 'halloween' });
I('teia', 'Teia de aranha', 'quadro', 20, 1, 1, { wall: true, ev: 'halloween' });
I('arvore', 'Árvore de Natal', 'movel', 100, 1, 1, { ev: 'natal' });
I('presente', 'Pilha de presentes', 'movel', 30, 1, 1, { ev: 'natal' });
I('meia', 'Meia de Natal', 'quadro', 20, 1, 1, { wall: true, ev: 'natal' });
I('bandeira', 'Bandeirinhas', 'quadro', 25, 1, 1, { wall: true, ev: 'junina' });
I('fogueira', 'Fogueirinha', 'movel', 40, 1, 1, { ev: 'junina' });
I('ovo', 'Ovo de Páscoa', 'movel', 30, 1, 1, { ev: 'pascoa' });
I('mascara', 'Máscara de carnaval', 'quadro', 30, 1, 1, { wall: true, ev: 'carnaval' });
I('fogos', 'Quadro de fogos', 'quadro', 40, 1, 1, { wall: true, ev: 'ano_novo' });
// pisos e paredes
I('piso_xadrez', 'Xadrez roxo', 'piso', 0, 1, 1, { free: true });
I('piso_madeira', 'Madeira', 'piso', 40);
I('piso_grama', 'Grama', 'piso', 50);
I('piso_azulejo', 'Azulejo', 'piso', 50);
I('piso_areia', 'Areia', 'piso', 60);
I('piso_neon', 'Pista neon', 'piso', 80);
I('piso_galaxia', 'Galáxia', 'piso', 120);
I('par_roxa', 'Roxo arcade', 'parede', 0, 1, 1, { free: true });
I('par_azul', 'Azul noite', 'parede', 40);
I('par_rosa', 'Rosa chiclete', 'parede', 40);
I('par_verde', 'Verde menta', 'parede', 40);
I('par_tijolo', 'Tijolinho', 'parede', 60);
I('par_memphis', 'Memphis', 'parede', 90);
I('par_estrelas', 'Céu de estrelas', 'parede', 110);
// bichinhos
I('pet_gato', 'Gatinho', 'pet', 80);
I('pet_cao', 'Cachorrinho', 'pet', 80);
I('pet_fantasma', 'Fantasminha', 'pet', 60);
I('pet_pintinho', 'Pintinho', 'pet', 50);
I('pet_robo', 'Robozinho', 'pet', 120);
I('pet_raposa', 'Raposa', 'pet', 150);
I('pet_dragao', 'Dragãozinho', 'pet', 300);
const CATMAP = {};
CAT.forEach(function (it) { CATMAP[it.id] = it; });
const CAT_PUB = CAT.map(function (it) { const o = { id: it.id, n: it.n, cat: it.cat, p: it.p, w: it.w, d: it.d }; if (it.flat) o.flat = 1; if (it.wall) o.wall = 1; if (it.ev) o.ev = it.ev; if (it.free) o.free = 1; return o; });
const ROOM_N = 8, ROOM_MAX_ITEMS = 60, OWN_MAX = 8;

function itemPrice(it) { if (it.free) return 0; return Math.max(1, Math.round(it.p * (1 - evSale()))); }
function itemOnShelf(it) { if (!it.ev) return true; const ev = EVENTS.find(function (e) { return e.id === it.ev; }); return !!ev && evActive(ev, true); }

function normItems(a) {
  const it = a.items && typeof a.items === 'object' ? a.items : {};
  it.own = it.own && typeof it.own === 'object' ? it.own : {};
  it.room = it.room && typeof it.room === 'object' ? it.room : {};
  it.room.floor = CATMAP[it.room.floor] && CATMAP[it.room.floor].cat === 'piso' ? it.room.floor : 'piso_xadrez';
  it.room.wall = CATMAP[it.room.wall] && CATMAP[it.room.wall].cat === 'parede' ? it.room.wall : 'par_roxa';
  it.room.put = Array.isArray(it.room.put) ? it.room.put : [];
  it.pet = typeof it.pet === 'string' && CATMAP[it.pet] && CATMAP[it.pet].cat === 'pet' ? it.pet : '';
  it.likes = it.likes && typeof it.likes === 'object' ? it.likes : {};
  it.visits = it.visits && typeof it.visits === 'object' ? it.visits : {};
  it.gal = Object.assign({ d: '', n: 0, total: 0, likes: 0 }, it.gal && typeof it.gal === 'object' ? it.gal : {});
  a.items = it;
  return it;
}
function itemsPub(a) {
  const it = a.items;
  return { own: it.own, room: it.room, pet: it.pet, likes: Object.keys(it.likes).length, visits: Object.keys(it.visits).length, gal: { total: it.gal.total, likes: it.gal.likes, d: it.gal.d, n: it.gal.n } };
}
function ownedOk(a, id) { const it = CATMAP[id]; return !!it && (it.free || (a.items.own[id] || 0) > 0); }

// valida e limpa o quarto enviado pelo cliente; devolve { room, pet } ou { err }
function cleanRoom(a, m) {
  if (!m || typeof m !== 'object') return { err: 'Quarto inválido.' };
  const floor = ownedOk(a, m.floor) && CATMAP[m.floor].cat === 'piso' ? m.floor : a.items.room.floor;
  const wall = ownedOk(a, m.wall) && CATMAP[m.wall].cat === 'parede' ? m.wall : a.items.room.wall;
  const pet = m.pet === '' ? '' : (typeof m.pet === 'string' && CATMAP[m.pet] && CATMAP[m.pet].cat === 'pet' && (a.items.own[m.pet] || 0) > 0 ? m.pet : a.items.pet);
  const put = [], count = {}, taken = {}, flatTaken = {}, wallTaken = {};
  const list = Array.isArray(m.put) ? m.put.slice(0, ROOM_MAX_ITEMS) : [];
  for (let i = 0; i < list.length; i++) {
    const q = list[i], it = q && CATMAP[q.id];
    if (!it || ['movel', 'tapete', 'quadro'].indexOf(it.cat) === -1) continue;
    if ((count[it.id] || 0) >= (a.items.own[it.id] || 0)) continue;
    if (it.wall) {
      const s = q.s === 'R' ? 'R' : 'L', ix = q.i | 0, k = s + ix;
      if (ix < 0 || ix >= ROOM_N || wallTaken[k]) continue;
      wallTaken[k] = 1; count[it.id] = (count[it.id] || 0) + 1;
      put.push({ id: it.id, s: s, i: ix });
    } else {
      const r = q.r ? 1 : 0, fw = r ? it.d : it.w, fd = r ? it.w : it.d, x = q.x | 0, y = q.y | 0;
      if (x < 0 || y < 0 || x + fw > ROOM_N || y + fd > ROOM_N) continue;
      const bag = it.flat ? flatTaken : taken;
      let clash = false;
      for (let yy = y; yy < y + fd && !clash; yy++) for (let xx = x; xx < x + fw; xx++) if (bag[xx + ',' + yy]) { clash = true; break; }
      if (clash) continue;
      for (let yy = y; yy < y + fd; yy++) for (let xx = x; xx < x + fw; xx++) bag[xx + ',' + yy] = 1;
      count[it.id] = (count[it.id] || 0) + 1;
      put.push({ id: it.id, x: x, y: y, r: r });
    }
  }
  return { room: { floor: floor, wall: wall, put: put }, pet: pet };
}

/* ---------- ações sobre contas, em memória ou no banco ---------- */
async function mutateAcct(key, fn) {
  const mem = playerByKey(key);
  if (mem && mem.acct) { fn(mem.acct); saveAcct(mem); return mem; }
  const a = await Store.getPlayer(key);
  if (!a) return null;
  normalizeAcct(a);
  fn(a);
  await Store.savePlayer(key, { coins: a.coins, total_coins: a.total_coins, xp: a.xp, items: a.items });
  return null;
}
async function loadAcct(key) {
  const mem = playerByKey(key);
  if (mem && mem.acct) return mem.acct;
  const a = await Store.getPlayer(key);
  return a ? normalizeAcct(a) : null;
}

/* ---------- lista de quartos ---------- */
let roomsCache = { t: 0, v: [] };
async function roomsList() {
  if (Date.now() - roomsCache.t < 15000) return roomsCache.v;
  const rows = await Store.listPlayers();
  const out = rows.map(function (r) {
    const mem = playerByKey(r.key), a = mem && mem.acct ? mem.acct : null;
    const it = a ? a.items : (r.items && typeof r.items === 'object' ? r.items : {});
    const put = it.room && Array.isArray(it.room.put) ? it.room.put.length : 0;
    const likes = it.likes && typeof it.likes === 'object' ? Object.keys(it.likes).length : 0;
    return { key: r.key, nick: a ? a.nick : r.nick, av: r.av || '', lv: lvOf(a ? a.xp : (r.xp | 0)), n: put, likes: likes };
  });
  out.sort(function (x, y) { return (y.likes - x.likes) || (y.n - x.n) || (y.lv - x.lv); });
  roomsCache = { t: Date.now(), v: out };
  return out;
}
function roomsOnline(list) {
  return list.map(function (r) { const m = playerByKey(r.key); return { nick: r.nick, av: r.av, lv: r.lv, n: r.n, likes: r.likes, on: !!(m && m.online) }; });
}

/* ---------- galeria ---------- */
let galCache = { t: 0, v: [] };
async function galAll() {
  if (Date.now() - galCache.t < 20000) return galCache.v;
  const v = await Store.galList(100);
  galCache = { t: Date.now(), v: v };
  return v;
}
function galPub(row, p) {
  const likes = row.likes && typeof row.likes === 'object' ? row.likes : {};
  return { id: row.id, nick: row.nick, word: row.word || '', theme: row.theme || '', img: row.img, n: row.n_likes | 0, liked: !!(p && likes[p.key]), mine: !!(p && row.key === p.key) };
}
const GAL_KEEP = 80, GAL_DAY = 5;
const IMG_RE = /^data:image\/(png|jpeg|webp);base64,[A-Za-z0-9+\/=]+$/;

/* ---------- aplica o multiplicador de eventos nas moedas de partidas ---------- */
function boosted(coins) { const m = evMult(); return m > 1 ? Math.round(coins * m) : coins; }

/* ---------- servidor http e socket ---------- */

const server = http.createServer(function (req, res) {
  const url = (req.url || '/').split('?')[0];
  if (url === '/' || url === '/health') {
    res.writeHead(200, { 'Content-Type': 'text/plain; charset=utf-8', 'Cache-Control': 'no-store' });
    res.end('Servidor do Gartic Listening no ar. Jogadores conectados: ' + onlinePlayers().length + ' de ' + MAX_PLAYERS + '.');
    return;
  }
  if (url === '/admin/reset-pin') {
    const q = new URLSearchParams((req.url || '').split('?')[1] || '');
    const ok = ADMIN_KEY && q.get('key') === ADMIN_KEY;
    const key = cleanNick(q.get('nick')).toLowerCase();
    res.writeHead(ok ? 200 : 403, { 'Content-Type': 'text/plain; charset=utf-8', 'Cache-Control': 'no-store' });
    if (!ok) { res.end('Chave inválida ou ADMIN_KEY não configurada.'); return; }
    Store.getPlayer(key).then(function (a) {
      if (!a) { res.end('Apelido não encontrado: ' + key); return null; }
      const mem = playerByKey(key);
      if (mem && mem.acct) { mem.acct.hash = ''; mem.acct.salt = ''; }
      return Store.savePlayer(key, { hash: '', salt: '' }).then(function () { res.end('PIN zerado. No próximo login, ' + key + ' define um PIN novo.'); });
    }).catch(function (e) { res.end('Erro: ' + e.message); });
    return;
  }
  if (url === '/admin/gallery-delete') {
    const q = new URLSearchParams((req.url || '').split('?')[1] || '');
    const ok = ADMIN_KEY && q.get('key') === ADMIN_KEY;
    res.writeHead(ok ? 200 : 403, { 'Content-Type': 'text/plain; charset=utf-8', 'Cache-Control': 'no-store' });
    if (!ok) { res.end('Chave inválida ou ADMIN_KEY não configurada.'); return; }
    Store.galDel(q.get('id')).then(function () { galCache.t = 0; io.emit('gal_new', { id: 0 }); res.end('Obra ' + q.get('id') + ' apagada.'); }).catch(function (e) { res.end('Erro: ' + e.message); });
    return;
  }
  if (url === '/avatars') {
    const origin = req.headers.origin || '';
    const h = { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store' };
    if (!ALLOWED.length) h['Access-Control-Allow-Origin'] = '*';
    else if (ALLOWED.indexOf(origin) !== -1) { h['Access-Control-Allow-Origin'] = origin; h['Vary'] = 'Origin'; }
    res.writeHead(200, h);
    res.end(JSON.stringify({ taken: takenList() }));
    return;
  }
  res.writeHead(404, { 'Content-Type': 'text/plain; charset=utf-8' });
  res.end('Não encontrado.');
});

const io = new Server(server, {
  cors: { origin: ALLOWED.length ? ALLOWED : '*' },
  maxHttpBufferSize: 1e6
});

io.on('connection', function (socket) {
  socket.on('join', async function (data) {
    try {
      if (socket.data.key || socket.data.joining) return;
      socket.data.joining = true;
      const nick = cleanNick(data && data.nick);
      const err = nickError(nick);
      if (err) { socket.emit('join_error', { msg: err }); return; }
      const key = nick.toLowerCase();
      const pin = String((data && data.pin) || '').trim();
      if (!/^\d{4}$/.test(pin)) { socket.emit('join_error', { code: 'pin', msg: 'Digite um PIN de 4 números. Na primeira vez, ele cria a sua conta.' }); return; }
      const lock = fails[key];
      if (lock && lock.until > Date.now()) { socket.emit('join_error', { code: 'pin', msg: 'PIN errado várias vezes. Tente de novo em ' + Math.ceil((lock.until - Date.now()) / 60000) + ' min.' }); return; }
      const av = cleanAvatar(data && data.av);
      const checkRoom = function () {
        const q = playerByKey(key);
        if (q && q.online) { socket.emit('join_error', { msg: 'Esse apelido já está em uso por alguém na sala.' }); return false; }
        if (!q && room.players.length >= MAX_PLAYERS) { socket.emit('join_error', { msg: 'A sala está cheia (' + MAX_PLAYERS + ' jogadores).' }); return false; }
        if (av && avatarTaken(av, key)) { socket.emit('join_error', { code: 'av', msg: 'Esse visual já está em uso por outra pessoa. Escolha outro.', taken: takenList() }); return false; }
        return true;
      };
      if (!checkRoom()) return;
      let p = playerByKey(key);
      let acct = p && p.acct ? p.acct : null;
      let isNew = false;
      if (!acct) {
        try { acct = await Store.getPlayer(key); } catch (e) { console.error('banco', e.message); socket.emit('join_error', { msg: 'O banco de dados não respondeu. Tente de novo em instantes.' }); return; }
      }
      if (acct && acct.hash) {
        const ok = await checkPin(pin, acct);
        if (!ok) {
          const f = fails[key] || { n: 0, until: 0 };
          f.n++;
          if (f.n >= 5) { f.n = 0; f.until = Date.now() + 5 * 60000; }
          fails[key] = f;
          socket.emit('join_error', { code: 'pin', msg: f.until > Date.now() ? 'PIN errado várias vezes. Tente de novo em 5 min.' : 'PIN incorreto para esse apelido.' });
          return;
        }
        delete fails[key];
      } else if (acct) {
        acct.salt = crypto.randomBytes(8).toString('hex');
        acct.hash = await hashPin(pin, acct.salt);
        isNew = true;
        try { await Store.savePlayer(key, { salt: acct.salt, hash: acct.hash }); } catch (e) { console.error('banco', e.message); socket.emit('join_error', { msg: 'O banco de dados não respondeu. Tente de novo em instantes.' }); return; }
      } else {
        const salt = crypto.randomBytes(8).toString('hex');
        acct = { key: key, nick: nick, salt: salt, hash: await hashPin(pin, salt), av: av || '', coins: 0, xp: 0, total_coins: 0, ach: {}, stats: {}, items: {}, last_daily: '', streak: 0 };
        try { await Store.createPlayer(acct); } catch (e) { console.error('banco', e.message); socket.emit('join_error', { msg: 'O banco de dados não respondeu. Tente de novo em instantes.' }); return; }
        isNew = true;
      }
      normalizeAcct(acct);
      if (!checkRoom()) return;
      p = playerByKey(key);
      let returning = false;
      if (p) {
        if (p.offTimer) { clearTimeout(p.offTimer); p.offTimer = null; }
        if (av) p.av = av;
        p.id = socket.id;
        p.online = true;
        returning = true;
      } else {
        const t = freeTile();
        p = { nick: nick, key: key, av: av || (acct.av && !avatarTaken(acct.av, key) ? acct.av : ''), x: t.x, y: t.y, stats: newStats(), lastReact: 0, lastSay: 0, lastWalk: 0, id: socket.id, online: true, score: 0, gain: 0, guessed: false, offTimer: null, lastMsg: 0 };
        room.players.push(p);
      }
      p.acct = acct;
      if (av) acct.av = av;
      if (p.nick !== nick) { p.nick = nick; acct.nick = nick; }
      socket.data.key = key;
      socket.emit('joined', { nick: p.nick, av: p.av || '', players: publicPlayers(), phase: room.phase, isNew: isNew, achs: ACH_PUB, account: acctPayload(p), store: Store.kind, shop: CAT_PUB, events: eventsPayload() });
      sys(p.nick + (returning ? ' voltou.' : ' entrou.'));
      sendPlayers();
      sendStateTo(socket, p);
      saveAcct(p);
      dailyBonus(p);
    } catch (e) { console.error('join', e); try { socket.emit('join_error', { msg: 'Não foi possível entrar agora. Tente de novo.' }); } catch (e2) { /* segue */ } }
    finally { socket.data.joining = false; }
  });

  socket.on('run', function (m) {
    try { const p = playerOf(socket); if (p && p.id === socket.id) handleRun(p, m).catch(function (e) { console.error('run', e.message); }); } catch (e) { console.error('run', e); }
  });

  socket.on('duo_result', function (m) {
    try { const p = playerOf(socket); if (p && p.id === socket.id) handleDuoResult(p, m); } catch (e) { console.error('duo_result', e); }
  });

  socket.on('top', async function (game) {
    try {
      game = String(game || '');
      if (!TOP_GAMES.has(game)) return;
      const wk = weekKey();
      const res = await Promise.all([getTop(game, 'all'), getTop(game, wk)]);
      socket.emit('top', { game: game, all: res[0], week: res[1], wk: wk });
    } catch (e) { console.error('top', e.message); }
  });

  socket.on('me', function () {
    try { const p = playerOf(socket); if (p && p.acct) { socket.emit('account', acctPayload(p)); socket.emit('events', eventsPayload()); } } catch (e) { console.error('me', e); }
  });

  socket.on('play', function (id) {
    try { const p = playerOf(socket); if (p && p.id === socket.id) setPl(p, id); } catch (e) { console.error('play', e); }
  });

  socket.on('duo_find', function (id) {
    try {
      const p = playerOf(socket);
      if (!p || room.phase !== 'lobby') return;
      id = String(id || '');
      if (!DUO_IDS.has(id)) return;
      duoLeave(p);
      const wk = duoWait[id], q = wk && wk !== p.key ? playerByKey(wk) : null;
      if (q && q.online && q.id && q.duoWait === id) {
        delete duoWait[id]; q.duoWait = '';
        q.duoWith = p.key; p.duoWith = q.key; q.duoGame = id; p.duoGame = id;
        io.to(q.id).emit('duo_start', { id: id, role: 'host', opp: p.nick });
        socket.emit('duo_start', { id: id, role: 'guest', opp: q.nick });
      } else {
        duoWait[id] = p.key; p.duoWait = id;
        socket.emit('duo_wait', { id: id });
      }
    } catch (e) { console.error('duo_find', e); }
  });

  socket.on('duo_cancel', function () {
    try { const p = playerOf(socket); if (p) duoCancelWait(p); } catch (e) { console.error('duo_cancel', e); }
  });

  socket.on('duo_msg', function (m) {
    try {
      const p = playerOf(socket);
      if (!p || !p.duoWith || !m || typeof m !== 'object') return;
      const q = playerByKey(p.duoWith);
      if (!q || !q.id || q.duoWith !== p.key) return;
      if (JSON.stringify(m).length > 3000) return;
      io.to(q.id).emit('duo_msg', m);
    } catch (e) { console.error('duo_msg', e); }
  });

  socket.on('duo_end', function () {
    try { const p = playerOf(socket); if (p) duoLeave(p); } catch (e) { console.error('duo_end', e); }
  });

  socket.on('leave', function () {
    try {
      const p = playerOf(socket);
      socket.data.key = null;
      if (p && p.id === socket.id) { p.id = null; p.online = false; removePlayer(p); }
    } catch (e) { console.error('leave', e); }
  });

  socket.on('start', function (data) {
    try {
      const p = playerOf(socket);
      if (!p) return;
      startGame(socket, data);
    } catch (e) { console.error('start', e); }
  });

  socket.on('draw', function (m) {
    try {
      const p = playerOf(socket);
      if (!p || room.phase !== 'round' || p.key !== room.drawer) return;
      handleDraw(socket, m);
    } catch (e) { console.error('draw', e); }
  });

  socket.on('walk', function (m) {
    try {
      const p = playerOf(socket);
      if (!p || room.phase !== 'lobby' || !m) return;
      const now = Date.now();
      if (now - p.lastWalk < 120) return;
      p.lastWalk = now;
      const x = Math.floor(Number(m.x)), y = Math.floor(Number(m.y));
      if (!(x >= 0 && x < ROOM_W && y >= 0 && y < ROOM_H) || isBlocked(x, y)) return;
      if (spotTaken(x, y, p)) { socket.emit('walk_no', { x: p.x, y: p.y }); return; }
      p.x = x; p.y = y;
      sendPlayers();
    } catch (e) { console.error('walk', e); }
  });
  socket.on('say', function (txt) {
    try {
      const p = playerOf(socket);
      if (!p || room.phase !== 'lobby') return;
      const now = Date.now();
      if (now - p.lastSay < 700) return;
      p.lastSay = now;
      const text = String(txt || '').replace(/[\u0000-\u001f]/g, ' ').replace(/\s+/g, ' ').trim().slice(0, 80);
      if (!text) return;
      io.emit('say', { nick: p.nick, text: text });
    } catch (e) { console.error('say', e); }
  });
  socket.on('react', function (m) {
    try {
      const p = playerOf(socket);
      if (!p || room.phase !== 'round') return;
      const now = Date.now();
      if (now - p.lastReact < 500) return;
      const e = Math.floor(Number(m && m.e));
      if (!(e >= 0 && e < REACTS)) return;
      p.lastReact = now;
      const d = playerByKey(room.drawer);
      if (d && d !== p) d.stats.reacts++;
      io.emit('react', { nick: p.nick, e: e });
    } catch (err) { console.error('react', err); }
  });
  socket.on('skip', function () {
    try {
      const p = playerOf(socket);
      if (!p || room.phase !== 'round' || p.key !== room.drawer) return;
      if (room.players.some(function (q) { return q.guessed; })) return;
      if (!room.bag.length) room.bag = shuffle(room.cfg.words.slice());
      room.word = room.bag.pop();
      room.revealed = new Set();
      room.mask = makeMask();
      room.actions = [];
      room.cur = null;
      io.emit('round', roundPayload());
      io.to(socket.id).emit('word', { word: room.word });
    } catch (e) { console.error('skip', e); }
  });

  socket.on('guess', function (txt) {
    try {
      const p = playerOf(socket);
      if (!p) return;
      const now = Date.now();
      if (now - p.lastMsg < 250) return;
      p.lastMsg = now;
      const text = String(txt || '').replace(/\s+/g, ' ').trim().slice(0, 60);
      if (!text) return;
      if (room.phase === 'round' && p.key !== room.drawer && !p.guessed) {
        const t = norm(text);
        const w = norm(room.word);
        if (t && (t === w || (w.length >= 3 && (' ' + t + ' ').indexOf(' ' + w + ' ') !== -1))) {
          correctGuess(p);
          return;
        }
        if (w.length >= 5 && lev(t, w) <= 1) socket.emit('chat', { k: 'warn', text: 'Quase! Está perto.' });
        p.stats.misses++;
        io.emit('chat', { k: 'msg', nick: p.nick, text: text });
      } else if (room.phase === 'round') {
        // quem já sabe a palavra só conversa com quem também sabe
        room.players.forEach(function (q) {
          if (q.id && (q.guessed || q.key === room.drawer)) io.to(q.id).emit('chat', { k: 'msg', nick: p.nick, text: text, priv: true });
        });
      } else {
        io.emit('chat', { k: 'msg', nick: p.nick, text: text });
      }
    } catch (e) { console.error('guess', e); }
  });


  /* ---------- FASE 2: loja, quarto, galeria ---------- */
  function liveP() { const p = playerOf(socket); return p && p.id === socket.id && p.acct ? p : null; }

  socket.on('events', function () { try { socket.emit('events', eventsPayload()); } catch (e) { console.error('events', e); } });

  socket.on('shop_buy', function (m) {
    try {
      const p = liveP(); if (!p) return;
      const id = String((m && m.id) || ''), it = CATMAP[id], a = p.acct;
      const fail = function (msg) { socket.emit('shop_err', { id: id, msg: msg }); };
      if (!it || it.free) return fail('Esse item não existe.');
      if (!itemOnShelf(it)) return fail('Esse item só aparece na temporada dele.');
      const single = ['piso', 'parede', 'pet'].indexOf(it.cat) !== -1;
      const have = a.items.own[id] || 0;
      if (single && have) return fail('Você já tem esse item.');
      if (!single && have >= OWN_MAX) return fail('Limite de ' + OWN_MAX + ' unidades desse item.');
      const price = itemPrice(it);
      if (a.coins < price) return fail('Faltam ' + (price - a.coins) + ' moedas.');
      a.coins -= price;
      a.items.own[id] = have + 1;
      if (it.cat === 'pet' && !a.items.pet) { a.items.pet = id; sendPlayers(); }
      saveAcct(p);
      roomsCache.t = 0;
      socket.emit('shop_ok', { id: id, price: price, name: it.n });
      grant(p, { kind: 'shop', coins: 0, xp: 3, spent: price });
    } catch (e) { console.error('shop_buy', e); }
  });

  socket.on('room_save', function (m) {
    try {
      const p = liveP(); if (!p) return;
      const now = Date.now();
      if (p.lastRoomSave && now - p.lastRoomSave < 400) return;
      p.lastRoomSave = now;
      const a = p.acct, r = cleanRoom(a, m);
      if (r.err) { socket.emit('room_err', { msg: r.err }); return; }
      const petChanged = a.items.pet !== r.pet;
      a.items.room = r.room; a.items.pet = r.pet;
      saveAcct(p);
      roomsCache.t = 0;
      socket.emit('account', acctPayload(p));
      if (petChanged) sendPlayers();
      grant(p, { kind: 'room', coins: 0, xp: 0 });
    } catch (e) { console.error('room_save', e); }
  });

  socket.on('pet_set', function (id) {
    try {
      const p = liveP(); if (!p) return;
      id = String(id || '');
      if (id !== '' && !(CATMAP[id] && CATMAP[id].cat === 'pet' && p.acct.items.own[id] > 0)) return;
      if (p.acct.items.pet === id) return;
      p.acct.items.pet = id;
      saveAcct(p);
      socket.emit('account', acctPayload(p));
      sendPlayers();
      grant(p, { kind: 'room', coins: 0, xp: 0 });
    } catch (e) { console.error('pet_set', e); }
  });

  socket.on('rooms_list', async function () {
    try {
      if (!liveP()) return;
      const list = await roomsList();
      socket.emit('rooms_list', { list: roomsOnline(list) });
    } catch (e) { console.error('rooms_list', e.message); socket.emit('rooms_list', { list: [], err: true }); }
  });

  socket.on('room_get', async function (m) {
    try {
      const p = liveP(); if (!p) return;
      const key = cleanNick(m && m.nick).toLowerCase();
      if (!key) return;
      const a = key === p.key ? p.acct : await loadAcct(key);
      if (!a) { socket.emit('room_data', { err: 'Esse jogador não existe.' }); return; }
      const mine = key === p.key;
      socket.emit('room_data', { nick: a.nick || key, av: a.av || '', lv: lvOf(a.xp), room: a.items.room, pet: a.items.pet, likes: Object.keys(a.items.likes).length, liked: !!a.items.likes[p.key], mine: mine });
      if (!mine && !p.acct.items.visits[key]) {
        if (Object.keys(p.acct.items.visits).length < 80) p.acct.items.visits[key] = 1;
        saveAcct(p);
        grant(p, { kind: 'visit', coins: 0, xp: 4, nick: a.nick || key });
      }
    } catch (e) { console.error('room_get', e.message); socket.emit('room_data', { err: 'Não foi possível abrir esse quarto agora.' }); }
  });

  socket.on('room_like', async function (m) {
    try {
      const p = liveP(); if (!p) return;
      const key = cleanNick(m && m.nick).toLowerCase();
      if (!key || key === p.key) return;
      const a0 = await loadAcct(key);
      if (!a0) return;
      if (a0.items.likes[p.key]) { socket.emit('room_liked', { nick: a0.nick, likes: Object.keys(a0.items.likes).length, dup: true }); return; }
      const owner = await mutateAcct(key, function (a) { a.items.likes[p.key] = 1; a.coins += 2; a.total_coins += 2; });
      roomsCache.t = 0;
      const a1 = await loadAcct(key);
      socket.emit('room_liked', { nick: a1.nick, likes: Object.keys(a1.items.likes).length });
      if (owner) grant(owner, { kind: 'liked', coins: 0, xp: 5, by: p.nick, what: 'quarto' });
    } catch (e) { console.error('room_like', e.message); }
  });

  socket.on('gal_list', async function (m) {
    try {
      const p = liveP();
      const n = Math.max(1, Math.min(60, (m && m.n | 0) || 40));
      const list = await galAll();
      socket.emit('gal_list', { items: list.slice(0, n).map(function (r) { return galPub(r, p); }), n: n });
    } catch (e) { console.error('gal_list', e.message); socket.emit('gal_list', { items: [], err: true }); }
  });

  socket.on('gal_add', async function (m) {
    try {
      const p = liveP(); if (!p) return;
      const fail = function (msg) { socket.emit('gal_err', { msg: msg }); };
      const img = String((m && m.img) || '');
      if (img.length > 70000 || !IMG_RE.test(img)) return fail('Imagem inválida.');
      const a = p.acct, today = dayKey();
      if (a.items.gal.d !== today) { a.items.gal.d = today; a.items.gal.n = 0; }
      if (a.items.gal.n >= GAL_DAY) return fail('Você já publicou ' + GAL_DAY + ' obras hoje. Volte amanhã.');
      const now = Date.now();
      if (p.lastGal && now - p.lastGal < 3000) return;
      p.lastGal = now;
      const row = { key: p.key, nick: p.nick, word: String((m && m.word) || '').slice(0, 40), theme: String((m && m.theme) || '').slice(0, 30), img: img, likes: {}, n_likes: 0 };
      const saved = await Store.galAdd(row);
      if (!saved) return fail('Não foi possível publicar agora.');
      a.items.gal.n++; a.items.gal.total++;
      galCache.t = 0;
      try {
        const all = await galAll();
        for (let i = GAL_KEEP; i < all.length; i++) await Store.galDel(all[i].id);
        if (all.length > GAL_KEEP) galCache.t = 0;
      } catch (e) { /* a limpeza fica para a próxima */ }
      socket.emit('gal_ok', { id: saved.id });
      io.emit('gal_new', { id: saved.id });
      grant(p, { kind: 'gal', coins: 3, xp: 10 });
    } catch (e) { console.error('gal_add', e.message); try { socket.emit('gal_err', { msg: 'A galeria não respondeu. Rode o SQL da Fase 2 no Supabase.' }); } catch (e2) { /* segue */ } }
  });

  socket.on('gal_like', async function (m) {
    try {
      const p = liveP(); if (!p) return;
      const id = m && m.id;
      const row = await Store.galGet(id);
      if (!row || row.key === p.key) return;
      const likes = row.likes && typeof row.likes === 'object' ? row.likes : {};
      if (likes[p.key]) return;
      likes[p.key] = 1;
      const n = (row.n_likes | 0) + 1;
      await Store.galSet(id, { likes: likes, n_likes: n });
      galCache.t = 0;
      socket.emit('gal_liked', { id: id, n: n });
      const owner = await mutateAcct(row.key, function (a) { a.coins += 1; a.total_coins += 1; a.items.gal.likes += 1; });
      if (owner) grant(owner, { kind: 'liked', coins: 0, xp: 3, by: p.nick, what: 'desenho' });
    } catch (e) { console.error('gal_like', e.message); }
  });

  socket.on('gal_del', async function (m) {
    try {
      const p = liveP(); if (!p) return;
      const id = m && m.id;
      const row = await Store.galGet(id);
      if (!row || row.key !== p.key) return;
      await Store.galDel(id);
      galCache.t = 0;
      socket.emit('gal_deleted', { id: id });
      io.emit('gal_new', { id: 0 });
    } catch (e) { console.error('gal_del', e.message); }
  });

  socket.on('disconnect', function () {
    try {
      const p = playerOf(socket);
      if (!p || p.id !== socket.id) return;
      p.id = null;
      p.online = false;
      p.pl = '';
      duoLeave(p);
      saveAcct(p, true);
      p.offTimer = setTimeout(function () { removePlayer(p); }, GRACE_MS);
      if (room.phase === 'round' && room.drawer !== p.key && everyoneGuessed()) endRound('all');
      sendPlayers();
    } catch (e) { console.error('disconnect', e); }
  });
});

process.on('SIGTERM', function () {
  Promise.all(room.players.map(function (p) { return saveAcct(p, true); })).catch(function () { /* segue */ }).then(function () {
    if (Store.flush) Store.flush();
    process.exit(0);
  });
  setTimeout(function () { process.exit(0); }, 4000);
});
process.on('uncaughtException', function (e) { console.error('uncaughtException', e); });
process.on('unhandledRejection', function (e) { console.error('unhandledRejection', e); });

server.listen(PORT, function () {
  console.log('Servidor do Gartic Listening rodando na porta ' + PORT + '.');
  console.log(Store.kind === 'supabase' ? 'Banco: Supabase conectado.' : 'ATENÇÃO: sem Supabase configurado. Salvando em arquivo local (some se o servidor reiniciar na hospedagem grátis).');
  console.log(ALLOWED.length ? 'Aceitando conexões de: ' + ALLOWED.join(', ') : 'ALLOWED_ORIGIN vazio: aceitando conexões de qualquer site (modo de teste).');
});
