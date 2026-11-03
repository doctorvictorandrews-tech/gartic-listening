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
      sc: p.sc || 'arcade',
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
  { id: 'decorador', n: 'Decorador', d: 'Coloque 8 itens na sua casa.', c: 40, t: function (s, a) { return a.items.house.put.length >= 8; } },
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

function giveStarter(p) {
  const a = p.acct;
  if (!a) return;
  let gift = 0;
  if (!a.items.starter) gift = STARTER; else if (!a.items.starter2) gift = Math.max(0, STARTER - STARTER_OLD);
  a.items.starter = 1; a.items.starter2 = 1;
  if (!gift) return;
  a.coins += gift;
  saveAcct(p, true);
  try { io.to(p.id).emit('reward', { kind: 'starter', coins: gift, xp: 0, ach: [], lvUp: 0 }); io.to(p.id).emit('account', acctPayload(p)); } catch (e) { /* segue */ }
}
/* renda por passear: a cada 10 minutos online, 20 moedas (até 400 por dia) */
setInterval(function () {
  try {
    room.players.forEach(function (p) {
      if (!p.online || !p.acct || !p.id) return;
      p.presMin = (p.presMin || 0) + 1;
      if (p.presMin < 10) return;
      p.presMin = 0;
      const s = p.acct.stats, today = dayKey();
      if (!s.dayPres || s.dayPres.d !== today) s.dayPres = { d: today, n: 0 };
      if (s.dayPres.n >= 400) return;
      s.dayPres.n += 20;
      grant(p, { kind: 'pres', coins: 20, xp: 2 });
    });
  } catch (e) { console.error('pres', e); }
}, 60000);
function dailyBonus(p) {
  const a = p.acct, today = dayKey();
  if (a.last_daily === today) return;
  a.streak = a.last_daily === yesterdayKey() ? a.streak + 1 : 1;
  a.last_daily = today;
  grant(p, { kind: 'daily', coins: 60 + 10 * Math.min(a.streak, 7), xp: 20, streak: a.streak });
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
const RUN_COIN_CAP = 40, DAY_COIN_CAP = 400;

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
// ----- Fase 2.5: itens de casa e jardim -----
I('cadeira', 'Cadeira', 'movel', 25);
I('fogao', 'Fogão', 'movel', 70);
I('pia', 'Pia de cozinha', 'movel', 80, 2, 1);
I('guarda_roupa', 'Guarda-roupa', 'movel', 100);
I('privada', 'Vaso sanitário', 'movel', 60);
I('banheira', 'Banheira', 'movel', 120, 2, 1);
I('lavatorio', 'Lavatório', 'movel', 50);
I('chuveiro', 'Chuveiro', 'movel', 60);
I('arvore_j', 'Árvore de jardim', 'movel', 60);
I('canteiro', 'Canteiro de flores', 'movel', 35, 2, 1);
I('banco_j', 'Banco de jardim', 'movel', 45, 2, 1);
I('churrasqueira', 'Churrasqueira', 'movel', 90);
I('poste', 'Poste de luz', 'movel', 40);
I('cerca', 'Cerquinha', 'movel', 20);
I('piscina', 'Piscina', 'tapete', 260, 3, 2, { flat: true });
/* ===== Catálogo da Fase 4: móveis, quadros, pisos e paredes novos (dados puros, usados pelo servidor e pelo cliente) =====
   linha: [id, nome, cat, preço, largura, fundo, altura, grupo, flags, arte]
   flags: f = plano, w = parede, x = extra (não entra nas moedas iniciais)
   arte de chão: "x y w d z h cor" (caixa), "o x y z raio cor" (círculo), "e x y z rx ry cor" (elipse), separados por ;
   arte de parede: fragmento SVG 30x38 */
var CAT3 = [
  /* ---- sala ---- */
  ['sofa3', 'Sofá grande', 'movel', 120, 3, 1, 30, 'sala', '', '0 0 3 1 0 10 #3b6fd0;0 0 3 .3 10 18 #2f58a8;0 .3 .22 .7 10 10 #2f58a8;2.78 .3 .22 .7 10 10 #2f58a8;.22 .3 .85 .7 10 4 #5b8ae8;1.07 .3 .85 .7 10 4 #5b8ae8;1.92 .3 .86 .7 10 4 #5b8ae8'],
  ['sofa_l', 'Sofá de canto', 'movel', 150, 2, 2, 30, 'sala', '', '0 0 2 1 0 10 #1f9a8a;0 1 1 1 0 10 #1f9a8a;0 0 2 .3 10 18 #177a6e;0 0 .3 2 10 18 #177a6e;.3 .3 1.7 .7 10 4 #3fc0ae;.3 1 .7 1 10 4 #3fc0ae'],
  ['poltrona2', 'Poltrona laranja', 'movel', 60, 1, 1, 34, 'sala', '', '.05 .05 .9 .9 0 9 #e8782a;.05 .05 .9 .28 9 20 #c8621a;.05 .33 .2 .62 9 9 #d8701e;.75 .33 .2 .62 9 9 #d8701e;.25 .33 .5 .62 9 4 #f8a050'],
  ['banqueta', 'Banqueta', 'movel', 20, 1, 1, 22, 'sala', '', '.2 .2 .1 .1 0 14 #6a4318;.7 .2 .1 .1 0 14 #6a4318;.2 .7 .1 .1 0 14 #6a4318;.7 .7 .1 .1 0 14 #6a4318;.12 .12 .76 .76 14 6 #c98f45'],
  ['rack', 'Rack de TV', 'movel', 110, 2, 1, 46, 'sala', '', '0 .1 2 .8 0 14 #6a4318;.1 .9 .8 .02 3 8 #3a2410;.6 .3 .8 .4 14 4 #20202a;.7 .35 .6 .3 18 24 #15151c;.75 .65 .5 .02 22 16 #5fd0ff'],
  ['tv_plana', 'TV de tela plana', 'movel', 150, 1, 1, 50, 'sala', '', '.3 .3 .4 .4 0 4 #333;.45 .45 .1 .1 4 8 #333;.05 .4 .9 .12 12 34 #15151c;.1 .52 .8 .02 15 28 #5fd0ff;.1 .52 .35 .02 24 19 #bff0ff'],
  ['lareira', 'Lareira', 'movel', 180, 2, 1, 70, 'sala', '', '0 .1 2 .9 0 60 #9a4a30;.4 .98 1.2 .02 4 26 #1a0f0a;.6 .94 .8 .06 4 12 #f6b83a;.8 .94 .4 .06 4 20 #e63a00;0 0 2 1.05 60 6 #d8c8a8'],
  ['piano', 'Piano', 'movel', 300, 2, 1, 52, 'sala', 'x', '0 0 .1 .9 0 24 #111;1.9 0 .1 .9 0 24 #111;0 0 2 1 24 14 #1c1c24;.1 .55 1.8 .4 38 3 #fff;.1 .6 1.8 .05 41 2 #232323;0 0 2 .5 38 12 #1c1c24'],
  ['vaso_alto', 'Vaso alto', 'movel', 45, 1, 1, 80, 'sala', '', '.3 .3 .4 .4 0 22 #c25a2a;.2 .2 .6 .6 22 40 #3D9A3D;.35 .35 .3 .3 62 16 #5cc45a'],
  ['luminaria', 'Luminária de chão', 'movel', 40, 1, 1, 76, 'sala', '', '.3 .3 .4 .4 0 3 #333;.47 .47 .06 .06 3 55 #333;.25 .25 .5 .5 58 18 #F6D84A;.3 .3 .4 .4 76 2 #fff3b0'],
  ['cacto', 'Cacto', 'movel', 20, 1, 1, 44, 'sala', '', '.3 .3 .4 .4 0 12 #E85AA0;.4 .4 .2 .2 12 28 #3D9A3D;.6 .45 .15 .1 22 4 #3D9A3D;.25 .45 .15 .1 16 4 #3D9A3D'],
  ['samambaia', 'Samambaia', 'movel', 30, 1, 1, 60, 'sala', '', '.3 .3 .4 .4 0 14 #a8702e;.1 .1 .8 .8 14 20 #3D9A3D;.25 .25 .5 .5 34 14 #5cc45a;.4 .4 .2 .2 48 8 #7cdc7c'],
  ['mesa_centro', 'Mesa de centro', 'movel', 55, 2, 1, 18, 'sala', '', '.1 .15 .1 .1 0 12 #232323;1.8 .15 .1 .1 0 12 #232323;.1 .75 .1 .1 0 12 #232323;1.8 .75 .1 .1 0 12 #232323;0 .05 2 .9 12 4 #bfe9f5'],
  ['violao', 'Violão', 'movel', 70, 1, 1, 56, 'lazer', '', '.3 .4 .4 .15 6 24 #c98f45;.45 .45 .1 .08 30 24 #6a4318;.42 .54 .16 .02 14 8 #232323;.25 .35 .1 .1 0 8 #333'],
  ['globo', 'Globo terrestre', 'movel', 55, 1, 1, 40, 'sala', '', '.35 .35 .3 .3 0 4 #6a4318;.45 .45 .1 .1 4 12 #a8702e;o .5 .5 24 11 #2B7ac4;o .45 .45 26 4 #3D9A3D'],
  ['estatua', 'Estátua', 'movel', 120, 1, 1, 66, 'sala', '', '.2 .2 .6 .6 0 16 #bdbdbd;.35 .35 .3 .3 16 28 #e8e8e8;o .5 .5 50 7 #e8e8e8'],
  ['planta_g', 'Planta grande', 'movel', 70, 1, 1, 90, 'sala', '', '.25 .25 .5 .5 0 18 #a8702e;.45 .45 .1 .1 18 20 #6a4318;.1 .1 .8 .8 38 28 #3D9A3D;.25 .25 .5 .5 66 16 #5cc45a'],
  ['biblioteca', 'Estante grande', 'movel', 120, 2, 1, 80, 'escritorio', '', '0 .1 2 .6 0 78 #7a4a20;.08 .7 .35 .02 6 18 #E63A00;.45 .7 .3 .02 6 18 #2B4EC4;.8 .7 .4 .02 6 18 #D8D82E;1.25 .7 .3 .02 6 18 #3D9A3D;1.6 .7 .3 .02 6 18 #E85AA0;.08 .7 .3 .02 34 18 #2BC4C4;.42 .7 .4 .02 34 18 #F6D84A;.85 .7 .3 .02 34 18 #E63A00;1.2 .7 .5 .02 34 18 #3D9A3D'],
  ['aparador', 'Aparador', 'movel', 90, 2, 1, 36, 'sala', '', '0 .1 2 .8 0 30 #8a5a2a;0 .05 2 .9 30 4 #a8702e;.45 .9 .06 .02 14 8 #F6D84A;1.45 .9 .06 .02 14 8 #F6D84A;.98 .9 .04 .02 2 26 #4a2a10'],
  /* ---- quarto ---- */
  ['cama_casal', 'Cama de casal', 'movel', 180, 2, 2, 36, 'quarto', '', '0 0 2 2 0 8 #8a5a2a;.05 .05 1.9 1.9 8 8 #f2f2f2;.05 .55 1.9 1.4 8 9 #5b8ae8;.2 .1 .6 .4 16 5 #fff;1.2 .1 .6 .4 16 5 #fff;0 0 2 .15 8 28 #6a4318'],
  ['beliche', 'Beliche', 'movel', 200, 1, 2, 74, 'quarto', '', '.02 .02 .1 .1 0 70 #6a4318;.88 .02 .1 .1 0 70 #6a4318;.02 1.88 .1 .1 0 70 #6a4318;.88 1.88 .1 .1 0 70 #6a4318;.05 .1 .9 1.8 10 6 #f2f2f2;.05 .6 .9 1.3 10 8 #2B4EC4;.05 .1 .9 1.8 40 6 #fff;.05 .6 .9 1.3 40 8 #E63A00'],
  ['criado', 'Criado-mudo', 'movel', 40, 1, 1, 30, 'quarto', '', '.12 .12 .76 .76 0 20 #8a5a2a;.08 .08 .84 .84 20 4 #a8702e;.45 .88 .1 .02 10 4 #F6D84A;.4 .4 .2 .2 24 8 #F6D84A'],
  ['comoda', 'Cômoda', 'movel', 100, 2, 1, 38, 'quarto', '', '0 .1 2 .8 0 34 #7a4a20;0 .05 2 .9 34 4 #a8702e;.1 .9 .8 .02 6 12 #5a3a18;1.1 .9 .8 .02 6 12 #5a3a18;.1 .9 .8 .02 20 12 #5a3a18;1.1 .9 .8 .02 20 12 #5a3a18;.45 .91 .1 .02 10 3 #F6D84A;1.45 .91 .1 .02 24 3 #F6D84A'],
  ['penteadeira', 'Penteadeira', 'movel', 110, 2, 1, 62, 'quarto', '', '0 .2 .1 .7 0 24 #f0d0d8;1.9 .2 .1 .7 0 24 #f0d0d8;0 .2 2 .7 24 4 #f8e0e8;.5 .25 1 .05 28 34 #6a4318;.55 .31 .9 .02 32 26 #bfe9f5'],
  ['ursinho', 'Ursinho de pelúcia', 'movel', 30, 1, 1, 28, 'quarto', '', '.3 .3 .4 .4 0 14 #b8793a;o .5 .5 20 7 #b8793a;.3 .3 .1 .1 24 4 #8a5a2a;.6 .3 .1 .1 24 4 #8a5a2a'],
  ['cesto', 'Cesto de roupa', 'movel', 20, 1, 1, 30, 'quarto', '', '.2 .2 .6 .6 0 24 #c98f45;.25 .25 .5 .5 24 2 #f2f2f2'],
  ['rede', 'Rede de dormir', 'movel', 90, 2, 1, 38, 'jardim', '', '.02 .4 .1 .1 0 40 #8a5a2a;1.88 .4 .1 .1 0 40 #8a5a2a;.1 .3 1.8 .4 14 5 #E85AA0;.1 .35 1.8 .3 19 3 #f8a0c8'],
  ['espelho_pe', 'Espelho de chão', 'movel', 60, 1, 1, 80, 'quarto', '', '.15 .4 .7 .1 0 78 #6a4318;.2 .52 .6 .02 4 70 #bfe9f5;.2 .52 .25 .02 40 34 #fff'],
  ['puff_cama', 'Banco de pé de cama', 'movel', 40, 2, 1, 18, 'quarto', '', '0 .1 2 .8 0 10 #6a4318;.05 .15 1.9 .7 10 6 #d9437a'],
  /* ---- cozinha ---- */
  ['balcao', 'Balcão', 'movel', 90, 2, 1, 40, 'cozinha', '', '0 .05 2 .9 0 32 #c9a06a;0 0 2 1 32 4 #e8e8f0;.1 .95 .8 .02 4 24 #8a6a3a;1.1 .95 .8 .02 4 24 #8a6a3a'],
  ['ilha', 'Ilha de cozinha', 'movel', 130, 2, 1, 42, 'cozinha', '', '0 .1 2 .8 0 34 #2B4EC4;0 0 2 1 34 5 #f2f2f2;.9 .9 .2 .1 12 12 #1f3a8a'],
  ['armario', 'Armário de cozinha', 'movel', 70, 1, 1, 76, 'cozinha', '', '.05 .05 .9 .9 0 70 #e8d8b8;.05 .05 .9 .9 70 4 #d8c8a8;.1 .95 .38 .02 6 58 #c8b898;.52 .95 .38 .02 6 58 #c8b898'],
  ['microondas', 'Micro-ondas', 'movel', 50, 1, 1, 34, 'cozinha', '', '.1 .1 .8 .8 0 14 #8a5a2a;.15 .2 .7 .6 14 18 #cfcfd6;.2 .8 .5 .02 17 12 #232323;.75 .8 .08 .02 18 10 #3fd070'],
  ['mesa_redonda', 'Mesa redonda', 'movel', 110, 2, 2, 28, 'cozinha', '', '.8 .8 .4 .4 0 22 #6a4318;e 1 1 24 30 15 #c98f45;e 1 1 26 24 12 #d8a055'],
  ['banqueta_bar', 'Banqueta de bar', 'movel', 30, 1, 1, 38, 'cozinha', '', '.45 .45 .1 .1 0 26 #888;.25 .25 .5 .5 26 6 #E63A00;.3 .3 .4 .4 0 3 #666'],
  ['fruteira', 'Fruteira', 'movel', 25, 1, 1, 22, 'cozinha', '', '.1 .1 .8 .8 0 12 #8a5a2a;o .35 .5 18 5 #E63A00;o .55 .45 18 5 #F6D84A;o .5 .6 17 5 #3D9A3D'],
  ['geladeira_g', 'Geladeira grande', 'movel', 190, 1, 1, 90, 'cozinha', '', '.1 .1 .8 .8 0 88 #e8e8f0;.1 .9 .8 .02 44 2 #999;.75 .9 .06 .02 50 20 #888;.75 .9 .06 .02 10 14 #888'],
  ['mesa_madeira', 'Mesa de madeira', 'movel', 130, 2, 2, 30, 'cozinha', '', '.1 .1 .1 .1 0 24 #6a4318;1.8 .1 .1 .1 0 24 #6a4318;.1 1.8 .1 .1 0 24 #6a4318;1.8 1.8 .1 .1 0 24 #6a4318;.05 .05 1.9 1.9 24 6 #b9803a;.8 .8 .4 .4 30 3 #fff'],
  /* ---- banheiro ---- */
  ['pia_b', 'Pia de banheiro', 'movel', 90, 2, 1, 44, 'banheiro', '', '0 .1 2 .8 0 30 #e8e8f0;0 0 2 1 30 4 #f2f2f2;.2 .2 .6 .6 33 2 #8fb4c8;1.2 .2 .6 .6 33 2 #8fb4c8;.45 .1 .1 .1 34 9 #9a9aa4;1.45 .1 .1 .1 34 9 #9a9aa4'],
  ['tapete_b', 'Tapete de banheiro', 'tapete', 25, 2, 1, 2, 'banheiro', 'f', '0 0 2 1 0 2 #6bd0e8;.1 .1 1.8 .8 2 1 #8ae0f4'],
  ['lixeira', 'Lixeira', 'movel', 15, 1, 1, 24, 'banheiro', '', '.3 .3 .4 .4 0 20 #9a9aa4;.28 .28 .44 .44 20 3 #bdbdc8'],
  ['balanca', 'Balança', 'tapete', 20, 1, 1, 6, 'banheiro', 'f', '.2 .2 .6 .6 0 5 #cfcfd6;.35 .35 .3 .15 5 1 #232323'],
  ['armario_b', 'Armário de banheiro', 'movel', 60, 1, 1, 60, 'banheiro', '', '.1 .1 .8 .8 0 56 #f2f2f2;.1 .9 .8 .02 4 52 #cfcfd6;.45 .91 .1 .02 24 10 #888'],
  ['hidro', 'Banheira de hidromassagem', 'movel', 280, 2, 2, 30, 'banheiro', 'x', '0 0 2 2 0 24 #e8e8f0;.1 .1 1.8 1.8 24 2 #5ad0f0;.3 .3 .4 .4 26 4 #bff0ff;1.2 .8 .3 .3 26 3 #bff0ff;1.7 0 .3 .3 24 10 #9a9aa4'],
  ['box_ch', 'Box de chuveiro', 'movel', 120, 1, 1, 80, 'banheiro', '', '.05 .05 .06 .06 0 78 #bbb;.89 .05 .06 .06 0 78 #bbb;.05 .89 .06 .06 0 78 #bbb;.89 .89 .06 .06 0 78 #bbb;.3 .3 .4 .4 70 5 #bbb;.45 .45 .1 .1 60 10 #bbb'],
  /* ---- escritório ---- */
  ['escrivaninha', 'Escrivaninha', 'movel', 110, 2, 1, 30, 'escritorio', '', '0 .05 .1 .9 0 24 #8a5a2a;1.9 .05 .1 .9 0 24 #8a5a2a;0 .05 2 .9 24 4 #c98f45;1.5 .1 .4 .8 4 20 #7a4a20;1.5 .95 .3 .02 12 6 #F6D84A'],
  ['cadeira_g', 'Cadeira gamer', 'movel', 130, 1, 1, 50, 'escritorio', '', '.3 .3 .4 .4 0 6 #232323;.15 .15 .7 .7 6 8 #E63A00;.15 .15 .7 .2 14 30 #E63A00;.25 .15 .5 .2 44 8 #232323'],
  ['arquivo', 'Arquivo', 'movel', 70, 1, 1, 50, 'escritorio', '', '.1 .1 .8 .8 0 48 #8a9098;.1 .9 .8 .02 24 2 #555;.1 .9 .8 .02 4 2 #555;.4 .91 .2 .02 32 4 #333;.4 .91 .2 .02 12 4 #333'],
  ['impressora', 'Impressora', 'movel', 60, 1, 1, 28, 'escritorio', '', '.1 .1 .8 .8 0 14 #8a5a2a;.15 .2 .7 .6 14 10 #d6d6dc;.2 .3 .6 .4 24 2 #fff'],
  ['lousa', 'Lousa móvel', 'movel', 70, 1, 1, 70, 'escritorio', '', '.1 .45 .06 .06 0 24 #888;.84 .45 .06 .06 0 24 #888;.05 .45 .9 .06 24 42 #8a5a2a;.1 .52 .8 .02 28 34 #f2f2f2;.15 .52 .3 .02 50 2 #E63A00'],
  ['mesa_reuniao', 'Mesa de reunião', 'movel', 160, 3, 1, 28, 'escritorio', '', '.1 .1 .1 .8 0 22 #232323;2.8 .1 .1 .8 0 22 #232323;0 .05 3 .9 22 5 #3a3a48'],
  ['setup', 'Setup duplo', 'movel', 200, 2, 1, 50, 'escritorio', '', '0 .1 .1 .8 0 24 #333;1.9 .1 .1 .8 0 24 #333;0 .05 2 .9 24 4 #232323;.1 .4 .7 .08 28 24 #15151c;.12 .5 .66 .02 31 18 #5fd0ff;1.1 .4 .7 .08 28 24 #15151c;1.12 .5 .66 .02 31 18 #7cffc8'],
  /* ---- jardim ---- */
  ['palmeira', 'Palmeira', 'movel', 90, 1, 1, 100, 'jardim', '', '.42 .42 .16 .16 0 62 #8a5a2a;0 .4 1 .2 62 4 #3D9A3D;.4 0 .2 1 62 4 #3D9A3D;.3 .3 .4 .4 66 6 #5cc45a'],
  ['arbusto', 'Arbusto', 'movel', 25, 1, 1, 36, 'jardim', '', '.1 .1 .8 .8 0 28 #3D9A3D;.2 .2 .6 .6 28 6 #5cc45a'],
  ['pinheiro', 'Pinheiro', 'movel', 70, 1, 1, 110, 'jardim', '', '.44 .44 .12 .12 0 20 #6a4318;.1 .1 .8 .8 14 22 #2a7a3a;.2 .2 .6 .6 36 22 #2a8a3a;.3 .3 .4 .4 58 22 #36a046;.4 .4 .2 .2 80 22 #44b454'],
  ['ipe', 'Ipê amarelo', 'movel', 110, 1, 1, 96, 'jardim', '', '.44 .44 .12 .12 0 48 #7a4a20;.0 .0 1 1 44 22 #f6d84a;.15 .15 .7 .7 66 14 #f8e46a'],
  ['fonte', 'Fonte', 'movel', 250, 2, 2, 40, 'jardim', 'x', '0 0 2 2 0 12 #bdbdbd;.1 .1 1.8 1.8 12 2 #5ad0f0;.85 .85 .3 .3 14 20 #bdbdbd;.6 .6 .8 .8 34 5 #bdbdbd;.9 .9 .2 .2 39 6 #bff0ff'],
  ['lago', 'Laguinho', 'tapete', 150, 3, 2, 2, 'jardim', 'fx', '0 0 3 2 0 2 #2a7ac4;.1 .1 2.8 1.8 2 1 #3a8ad4;.6 .5 .4 .4 3 1 #3D9A3D;1.8 1 .4 .4 3 1 #3D9A3D'],
  ['balanco', 'Balanço', 'movel', 100, 2, 1, 70, 'jardim', '', '0 .4 .1 .1 0 66 #8a5a2a;1.9 .4 .1 .1 0 66 #8a5a2a;0 .4 2 .1 62 5 #8a5a2a;.45 .45 .03 .03 22 40 #232323;1.5 .45 .03 .03 22 40 #232323;.35 .35 .4 .3 18 4 #E63A00;1.35 .35 .4 .3 18 4 #2B4EC4'],
  ['mesa_jardim', 'Mesa de jardim', 'movel', 120, 2, 2, 30, 'jardim', '', '.9 .9 .2 .2 0 22 #bbb;e 1 1 24 30 15 #f2f2f2;e 1 1 26 24 12 #e0e0e8'],
  ['guarda_sol', 'Guarda-sol', 'movel', 60, 1, 1, 90, 'jardim', '', '.46 .46 .08 .08 0 70 #bbb;0 0 1 1 70 6 #E63A00;.2 .2 .6 .6 76 5 #fff;.35 .35 .3 .3 81 4 #E63A00'],
  ['espreguicadeira', 'Espreguiçadeira', 'movel', 80, 1, 2, 26, 'jardim', '', '.1 0 .8 2 0 8 #2BC4C4;.1 0 .8 .6 8 14 #1fa5a5;.1 .6 .8 1.4 8 3 #7cdcdc'],
  ['hortinha', 'Horta', 'movel', 45, 2, 1, 18, 'jardim', '', '0 .1 2 .8 0 10 #5a3a1a;.15 .3 .3 .4 10 8 #3D9A3D;.7 .3 .3 .4 10 8 #E63A00;1.2 .3 .3 .4 10 8 #5cc45a'],
  ['pedras', 'Pedras', 'movel', 15, 1, 1, 14, 'jardim', '', '.1 .2 .4 .4 0 10 #8a8f98;.5 .4 .4 .4 0 7 #9aa0a8;.3 .1 .3 .3 0 6 #a8aeb6'],
  ['lanterna', 'Lanterna de jardim', 'movel', 35, 1, 1, 40, 'jardim', '', '.4 .4 .2 .2 0 20 #6a6a74;.35 .35 .3 .3 20 12 #F6D84A;.3 .3 .4 .4 32 4 #333'],
  ['cerca_l', 'Cerca longa', 'movel', 40, 3, 1, 26, 'jardim', '', '.05 .4 .1 .2 0 26 #fff;1.45 .4 .1 .2 0 26 #fff;2.85 .4 .1 .2 0 26 #fff;0 .45 3 .1 16 4 #f2f2f2;0 .45 3 .1 6 4 #f2f2f2'],
  ['portao', 'Portãozinho', 'movel', 45, 2, 1, 30, 'jardim', '', '0 .4 .1 .2 0 30 #8a5a2a;1.9 .4 .1 .2 0 30 #8a5a2a;.1 .45 1.8 .1 18 4 #a8702e;.1 .45 1.8 .1 6 4 #a8702e;.9 .45 .1 .1 6 16 #a8702e'],
  ['correio', 'Caixa de correio', 'movel', 30, 1, 1, 44, 'jardim', '', '.46 .46 .08 .08 0 28 #6a4318;.25 .3 .5 .4 28 14 #E63A00;.25 .7 .5 .02 30 8 #b82e00'],
  ['casinha', 'Casinha de cachorro', 'movel', 70, 1, 1, 36, 'jardim', '', '.1 .1 .8 .8 0 22 #c25a2a;0 0 1 1 22 6 #6a4318;.3 .9 .4 .02 2 14 #1a0f0a'],
  ['gazebo', 'Gazebo', 'movel', 300, 3, 3, 96, 'jardim', 'x', '.05 .05 .12 .12 0 82 #f2f2f2;2.83 .05 .12 .12 0 82 #f2f2f2;.05 2.83 .12 .12 0 82 #f2f2f2;2.83 2.83 .12 .12 0 82 #f2f2f2;0 0 3 3 82 8 #E63A00;.4 .4 2.2 2.2 90 6 #f2f2f2'],
  ['trampolim', 'Cama elástica', 'movel', 160, 2, 2, 22, 'jardim', 'x', '.1 .1 .1 .1 0 14 #555;1.8 .1 .1 .1 0 14 #555;.1 1.8 .1 .1 0 14 #555;1.8 1.8 .1 .1 0 14 #555;e 1 1 16 30 15 #232323;e 1 1 18 24 12 #2B4EC4'],
  ['piscina2', 'Piscina grande', 'tapete', 380, 4, 3, 2, 'jardim', 'fx', '0 0 4 3 0 2 #e8e8f0;.15 .15 3.7 2.7 2 1 #3fb4ea;.3 .3 3.4 2.4 3 1 #5ad0f0;.6 .5 .8 .5 4 1 #bff0ff'],
  ['barraca', 'Barraca de camping', 'movel', 140, 2, 2, 50, 'jardim', '', '0 0 2 2 0 8 #E8782A;.2 .2 1.6 1.6 8 10 #E8782A;.4 .4 1.2 1.2 18 10 #f09a50;.6 .6 .8 .8 28 10 #E8782A'],
  ['fogueira2', 'Fogueira de acampamento', 'movel', 40, 1, 1, 24, 'jardim', '', '.15 .15 .7 .1 0 6 #6a4318;.15 .75 .7 .1 0 6 #6a4318;.3 .3 .4 .4 4 8 #E63A00;.4 .4 .2 .2 10 12 #F6D84A'],
  ['bike', 'Bicicleta', 'movel', 90, 1, 2, 40, 'jardim', '', '.4 .1 .2 .5 0 24 #232323;.4 1.4 .2 .5 0 24 #232323;.4 .5 .2 1 14 4 #E63A00;.35 .3 .3 .2 24 4 #232323;.3 1.5 .4 .1 28 3 #232323'],
  /* ---- lazer ---- */
  ['sinuca', 'Mesa de sinuca', 'movel', 300, 3, 2, 34, 'lazer', 'x', '.1 .1 .2 .2 0 24 #6a4318;2.7 .1 .2 .2 0 24 #6a4318;.1 1.7 .2 .2 0 24 #6a4318;2.7 1.7 .2 .2 0 24 #6a4318;0 0 3 2 24 8 #6a4318;.15 .15 2.7 1.7 28 4 #1f8a4a;o 1 .8 34 2 #fff;o 1.8 1.1 34 2 #E63A00'],
  ['pebolim', 'Pebolim', 'movel', 160, 2, 1, 30, 'lazer', '', '.1 .15 .1 .7 0 14 #333;1.8 .15 .1 .7 0 14 #333;0 .05 2 .9 14 10 #2B4EC4;.05 .1 1.9 .8 24 2 #1f8a4a;.4 0 .1 1 26 2 #E63A00;1.2 0 .1 1 26 2 #D8D82E'],
  ['pingue', 'Mesa de ping-pong', 'movel', 150, 3, 2, 30, 'lazer', 'x', '.1 .1 .1 .1 0 22 #333;2.8 .1 .1 .1 0 22 #333;.1 1.8 .1 .1 0 22 #333;2.8 1.8 .1 .1 0 22 #333;0 0 3 2 22 3 #1f6ad0;1.45 0 .1 2 25 8 #f2f2f2;1.4 0 .02 2 25 .5 #fff'],
  ['xadrez', 'Mesa de xadrez', 'movel', 70, 1, 1, 34, 'lazer', '', '.4 .4 .2 .2 0 22 #6a4318;.1 .1 .8 .8 22 3 #f2f2f2;.1 .1 .2 .2 25 1 #232323;.5 .1 .2 .2 25 1 #232323;.3 .3 .2 .2 25 1 #232323;.1 .5 .2 .2 25 1 #232323;.5 .5 .2 .2 25 1 #232323;o .3 .3 30 3 #E63A00;o .7 .7 30 3 #232323'],
  ['arcade2', 'Fliperama clássico', 'movel', 200, 1, 1, 82, 'lazer', '', '.1 .1 .8 .8 0 70 #2B4EC4;.2 .9 .6 .02 38 22 #0b2a22;.25 .91 .5 .02 40 18 #7CFFC8;.1 .1 .8 .8 70 8 #F15A1A;.2 .85 .6 .08 30 6 #E63A00;.4 .88 .08 .08 34 4 #F6D84A'],
  ['karaoke', 'Karaokê', 'movel', 120, 1, 1, 60, 'lazer', '', '.3 .4 .4 .3 0 4 #333;.46 .5 .08 .08 4 40 #333;.4 .45 .2 .2 44 12 #232323;.7 .4 .3 .1 0 36 #15151c;.75 .5 .2 .02 8 24 #7CFFC8'],
  ['dj', 'Mesa de DJ', 'movel', 220, 2, 1, 46, 'lazer', 'x', '0 .1 .1 .8 0 30 #232323;1.9 .1 .1 .8 0 30 #232323;0 .05 2 .9 30 6 #3a3a48;.2 .3 .5 .5 36 3 #15151c;1.3 .3 .5 .5 36 3 #15151c;o .45 .55 40 6 #F15A1A;o 1.55 .55 40 6 #2BC4C4'],
  ['poker', 'Mesa de pôquer', 'movel', 180, 2, 2, 28, 'lazer', '', '.8 .8 .4 .4 0 22 #6a4318;e 1 1 24 30 15 #1f8a4a;e 1 1 26 26 13 #2aa05a;o .6 .8 28 3 #E63A00;o 1.4 1.1 28 3 #2B4EC4'],
  ['cabine', 'Cabine de fotos', 'movel', 200, 1, 1, 90, 'lazer', 'x', '.05 .05 .9 .9 0 84 #E63A00;.05 .05 .9 .9 84 6 #232323;.15 .9 .7 .02 20 50 #1a0f2a;.3 .92 .4 .02 40 14 #F6D84A'],
  /* ---- decoração de parede ---- */
  ['janela1', 'Janela', 'quadro', 50, 1, 1, 0, 'decor', 'w', '<rect width="30" height="38" fill="#e8e0d0"/><rect x="3" y="3" width="24" height="32" fill="#8fd0f5"/><rect x="14" y="3" width="2" height="32" fill="#e8e0d0"/><rect x="3" y="18" width="24" height="2" fill="#e8e0d0"/><rect x="5" y="5" width="6" height="8" fill="#fff" opacity=".5"/>'],
  ['janela2', 'Janela redonda', 'quadro', 60, 1, 1, 0, 'decor', 'w', '<circle cx="15" cy="19" r="16" fill="#6a4318"/><circle cx="15" cy="19" r="13" fill="#8fd0f5"/><rect x="14" y="6" width="2" height="26" fill="#6a4318"/><rect x="2" y="18" width="26" height="2" fill="#6a4318"/><circle cx="10" cy="13" r="3" fill="#fff" opacity=".6"/>'],
  ['janela3', 'Janela com cortina', 'quadro', 80, 1, 1, 0, 'decor', 'w', '<rect width="30" height="38" fill="#e8e0d0"/><rect x="3" y="3" width="24" height="32" fill="#8fd0f5"/><rect x="2" y="2" width="9" height="34" fill="#E85AA0"/><rect x="19" y="2" width="9" height="34" fill="#E85AA0"/><rect x="5" y="2" width="2" height="34" fill="#c84880"/><rect x="22" y="2" width="2" height="34" fill="#c84880"/>'],
  ['quadro4', 'Paisagem', 'quadro', 40, 1, 1, 0, 'decor', 'w', '<rect width="30" height="38" fill="#6a4318"/><rect x="3" y="3" width="24" height="32" fill="#8fd0f5"/><polygon points="3,35 12,16 20,35" fill="#5a7a5a"/><polygon points="12,35 21,12 27,35" fill="#44684a"/><rect x="3" y="28" width="24" height="7" fill="#3D9A3D"/><circle cx="22" cy="9" r="3" fill="#F6D84A"/>'],
  ['quadro5', 'Retrato', 'quadro', 40, 1, 1, 0, 'decor', 'w', '<rect width="30" height="38" fill="#a8702e"/><rect x="3" y="3" width="24" height="32" fill="#d8c8a8"/><circle cx="15" cy="16" r="6" fill="#f2c9a0"/><rect x="9" y="22" width="12" height="12" fill="#2B4EC4"/><rect x="9" y="9" width="12" height="4" fill="#5a3a1a"/>'],
  ['quadro6', 'Flores', 'quadro', 35, 1, 1, 0, 'decor', 'w', '<rect width="30" height="38" fill="#232323"/><rect x="3" y="3" width="24" height="32" fill="#f8e8c8"/><rect x="14" y="16" width="2" height="16" fill="#3D9A3D"/><circle cx="15" cy="13" r="5" fill="#E85AA0"/><circle cx="15" cy="13" r="2" fill="#F6D84A"/><circle cx="8" cy="22" r="3" fill="#E63A00"/><circle cx="22" cy="24" r="3" fill="#8a2be2"/>'],
  ['quadro7', 'Gatinho', 'quadro', 40, 1, 1, 0, 'decor', 'w', '<rect width="30" height="38" fill="#232323"/><rect x="3" y="3" width="24" height="32" fill="#2BC4C4"/><rect x="9" y="12" width="12" height="12" fill="#F28C28"/><rect x="9" y="9" width="3" height="4" fill="#F28C28"/><rect x="18" y="9" width="3" height="4" fill="#F28C28"/><rect x="11" y="15" width="2" height="2" fill="#232323"/><rect x="17" y="15" width="2" height="2" fill="#232323"/><rect x="14" y="19" width="2" height="2" fill="#E85AA0"/>'],
  ['quadro8', 'Mapa-múndi', 'quadro', 45, 1, 1, 0, 'decor', 'w', '<rect width="30" height="38" fill="#6a4318"/><rect x="2" y="6" width="26" height="26" fill="#8fc4f0"/><polygon points="6,12 12,10 14,16 10,24 7,18" fill="#3D9A3D"/><polygon points="16,10 24,12 22,20 18,18" fill="#5cc45a"/><polygon points="14,22 18,22 17,29 14,28" fill="#3D9A3D"/>'],
  ['quadro9', 'Abstrato', 'quadro', 50, 1, 1, 0, 'decor', 'w', '<rect width="30" height="38" fill="#232323"/><rect x="3" y="3" width="24" height="32" fill="#f2f2f2"/><rect x="5" y="6" width="10" height="14" fill="#E63A00"/><rect x="12" y="14" width="12" height="10" fill="#2B4EC4" opacity=".85"/><circle cx="20" cy="9" r="4" fill="#F6D84A"/><rect x="6" y="26" width="18" height="3" fill="#232323"/>'],
  ['cuco', 'Relógio cuco', 'quadro', 80, 1, 1, 0, 'decor', 'w', '<polygon points="15,0 30,12 0,12" fill="#8a3a10"/><rect x="2" y="12" width="26" height="22" fill="#a8702e"/><circle cx="15" cy="23" r="8" fill="#f2f2f2"/><rect x="14" y="17" width="2" height="7" fill="#232323"/><rect x="15" y="23" width="5" height="2" fill="#232323"/><rect x="12" y="34" width="6" height="4" fill="#F6D84A"/>'],
  ['tv_parede', 'TV de parede', 'quadro', 120, 1, 1, 0, 'decor', 'w', '<rect y="6" width="30" height="20" fill="#15151c"/><rect x="2" y="8" width="26" height="16" fill="#5fd0ff"/><polygon points="2,8 14,8 6,24 2,24" fill="#bff0ff" opacity=".5"/><rect x="12" y="26" width="6" height="2" fill="#333"/>'],
  ['arandela', 'Arandela', 'quadro', 35, 1, 1, 0, 'decor', 'w', '<rect x="12" y="4" width="6" height="8" fill="#6a4318"/><polygon points="6,28 24,28 20,12 10,12" fill="#F6D84A"/><rect x="6" y="28" width="18" height="3" fill="#a8702e"/><circle cx="15" cy="32" r="6" fill="#fff3b0" opacity=".4"/>'],
  ['nicho', 'Nicho com plantas', 'quadro', 45, 1, 1, 0, 'decor', 'w', '<rect x="0" y="22" width="30" height="4" fill="#a8702e"/><rect x="4" y="12" width="8" height="10" fill="#c25a2a"/><rect x="2" y="2" width="12" height="10" fill="#3D9A3D"/><rect x="18" y="14" width="8" height="8" fill="#E85AA0"/><rect x="20" y="6" width="4" height="8" fill="#5cc45a"/>'],
  ['bandeira_br', 'Bandeira do Brasil', 'quadro', 60, 1, 1, 0, 'decor', 'w', '<rect x="1" y="6" width="28" height="20" fill="#2a9a3a"/><polygon points="15,9 26,16 15,23 4,16" fill="#F6D84A"/><circle cx="15" cy="16" r="5" fill="#2B4EC4"/><rect x="0" y="2" width="2" height="34" fill="#a8702e"/>'],
  ['guirlanda', 'Guirlanda', 'quadro', 40, 1, 1, 0, 'decor', 'w', '<circle cx="15" cy="17" r="14" fill="#2a7a3a"/><circle cx="15" cy="17" r="8" fill="#e8e0d0" opacity="0"/><circle cx="15" cy="17" r="7" fill="none"/><circle cx="8" cy="10" r="2" fill="#E63A00"/><circle cx="22" cy="12" r="2" fill="#E63A00"/><circle cx="21" cy="24" r="2" fill="#F6D84A"/><circle cx="9" cy="23" r="2" fill="#F6D84A"/><rect x="11" y="30" width="8" height="6" fill="#E63A00"/>'],
  ['dardos', 'Alvo de dardos', 'quadro', 40, 1, 1, 0, 'decor', 'w', '<circle cx="15" cy="19" r="15" fill="#232323"/><circle cx="15" cy="19" r="12" fill="#E63A00"/><circle cx="15" cy="19" r="8" fill="#f2f2f2"/><circle cx="15" cy="19" r="4" fill="#232323"/><circle cx="15" cy="19" r="1.5" fill="#E63A00"/><rect x="18" y="10" width="2" height="6" fill="#F6D84A"/>'],
  ['skate', 'Skate na parede', 'quadro', 50, 1, 1, 0, 'decor', 'w', '<rect x="10" y="0" width="10" height="38" fill="#E85AA0"/><rect x="12" y="4" width="6" height="30" fill="#2BC4C4"/><rect x="8" y="6" width="4" height="4" fill="#232323"/><rect x="18" y="6" width="4" height="4" fill="#232323"/><rect x="8" y="28" width="4" height="4" fill="#232323"/><rect x="18" y="28" width="4" height="4" fill="#232323"/>'],
  ['violao_p', 'Violão na parede', 'quadro', 60, 1, 1, 0, 'decor', 'w', '<rect x="13" y="0" width="4" height="20" fill="#6a4318"/><polygon points="6,34 8,22 22,22 24,34 15,38" fill="#c98f45"/><circle cx="15" cy="28" r="3" fill="#232323"/><rect x="12" y="2" width="6" height="4" fill="#232323"/>'],
  ['vinil', 'Disco de vinil', 'quadro', 35, 1, 1, 0, 'decor', 'w', '<circle cx="15" cy="19" r="15" fill="#15151c"/><circle cx="15" cy="19" r="11" fill="#232333"/><circle cx="15" cy="19" r="5" fill="#E63A00"/><circle cx="15" cy="19" r="1.5" fill="#15151c"/><path d="M6 14 q9 -9 18 0" fill="none" stroke="#fff" stroke-width="1" opacity=".4"/>'],
  ['placa', 'Placa LISTENING', 'quadro', 70, 1, 1, 0, 'decor', 'w', '<rect y="8" width="30" height="22" fill="#232323"/><rect x="2" y="10" width="26" height="18" fill="#F15A1A"/><rect x="5" y="14" width="20" height="3" fill="#232323"/><rect x="5" y="20" width="14" height="3" fill="#232323"/><rect x="21" y="20" width="4" height="3" fill="#F6D84A"/>'],
  ['recados', 'Quadro de recados', 'quadro', 35, 1, 1, 0, 'decor', 'w', '<rect width="30" height="38" fill="#6a4318"/><rect x="3" y="3" width="24" height="32" fill="#c98f45"/><rect x="6" y="7" width="8" height="8" fill="#F6D84A"/><rect x="16" y="9" width="8" height="8" fill="#E85AA0"/><rect x="8" y="20" width="9" height="8" fill="#5fd0ff"/><circle cx="10" cy="8" r="1.5" fill="#E63A00"/>'],
  ['espelho_r', 'Espelho redondo', 'quadro', 50, 1, 1, 0, 'decor', 'w', '<circle cx="15" cy="19" r="16" fill="#a8702e"/><circle cx="15" cy="19" r="13" fill="#bfe9f5"/><polygon points="6,24 10,12 16,6 22,8" fill="#fff" opacity=".4"/>'],
  /* ---- pisos ---- */
  ['piso_ceramica', 'Cerâmica bege', 'piso', 45, 1, 1, 0, 'estilo', '', ''],
  ['piso_marmore', 'Mármore', 'piso', 90, 1, 1, 0, 'estilo', '', ''],
  ['piso_taco', 'Tábua escura', 'piso', 60, 1, 1, 0, 'estilo', '', ''],
  ['piso_pedra', 'Pedra', 'piso', 50, 1, 1, 0, 'estilo', '', ''],
  ['piso_bw', 'Xadrez preto e branco', 'piso', 60, 1, 1, 0, 'estilo', '', ''],
  ['piso_rosa', 'Rosa pastel', 'piso', 40, 1, 1, 0, 'estilo', '', ''],
  ['piso_azul', 'Azul céu', 'piso', 40, 1, 1, 0, 'estilo', '', ''],
  ['piso_verde', 'Verde folha', 'piso', 40, 1, 1, 0, 'estilo', '', ''],
  ['piso_vermelho', 'Carpete vermelho', 'piso', 70, 1, 1, 0, 'estilo', '', ''],
  ['piso_cinza', 'Concreto', 'piso', 35, 1, 1, 0, 'estilo', '', ''],
  ['piso_lilas', 'Lilás', 'piso', 40, 1, 1, 0, 'estilo', '', ''],
  ['piso_terracota', 'Terracota', 'piso', 50, 1, 1, 0, 'estilo', '', ''],
  ['piso_gelo', 'Gelo', 'piso', 70, 1, 1, 0, 'estilo', '', ''],
  ['piso_amarelo', 'Amarelo sol', 'piso', 40, 1, 1, 0, 'estilo', '', ''],
  /* ---- paredes ---- */
  ['par_creme', 'Creme', 'parede', 40, 1, 1, 0, 'estilo', '', ''],
  ['par_cinza', 'Cinza', 'parede', 40, 1, 1, 0, 'estilo', '', ''],
  ['par_laranja', 'Laranja', 'parede', 40, 1, 1, 0, 'estilo', '', ''],
  ['par_vermelha', 'Vermelho', 'parede', 40, 1, 1, 0, 'estilo', '', ''],
  ['par_branca', 'Branco', 'parede', 40, 1, 1, 0, 'estilo', '', ''],
  ['par_preta', 'Preto', 'parede', 40, 1, 1, 0, 'estilo', '', ''],
  ['par_lilas', 'Lilás', 'parede', 40, 1, 1, 0, 'estilo', '', ''],
  ['par_amarela', 'Amarelo', 'parede', 40, 1, 1, 0, 'estilo', '', ''],
  ['par_madeira', 'Madeira', 'parede', 60, 1, 1, 0, 'estilo', '', ''],
  ['par_pedra', 'Pedra', 'parede', 60, 1, 1, 0, 'estilo', '', ''],
  ['par_celeste', 'Celeste', 'parede', 40, 1, 1, 0, 'estilo', '', ''],
  ['par_listras', 'Listras rosa', 'parede', 70, 1, 1, 0, 'estilo', '', ''],
  ['par_listras2', 'Listras azuis', 'parede', 70, 1, 1, 0, 'estilo', '', '']
];
/* cores de pisos e paredes novos (cliente) */
var FLOORS3 = {
  piso_ceramica: { a: '#e8dcc0', b: '#d8ccb0' }, piso_marmore: { a: '#f0f0f4', b: '#dcdce4', dots: '#c8c8d4' }, piso_taco: { a: '#6a4a30', b: '#5a3c26', plank: 1 },
  piso_pedra: { a: '#9aa0a8', b: '#8a9098', dots: '#70767e' }, piso_bw: { a: '#f2f2f2', b: '#232323' }, piso_rosa: { a: '#f0b8d0', b: '#e8a8c4' }, piso_azul: { a: '#8fc4f0', b: '#7ab4e4' },
  piso_verde: { a: '#7ac47a', b: '#6ab46a' }, piso_vermelho: { a: '#b02a2a', b: '#9a2222' }, piso_cinza: { a: '#9a9aa4', b: '#8e8e98' }, piso_lilas: { a: '#b8a0e0', b: '#a890d4' },
  piso_terracota: { a: '#d8884a', b: '#c87a3e' }, piso_gelo: { a: '#d0f0ff', b: '#b8e4f8', stars: 1 }, piso_amarelo: { a: '#f0d868', b: '#e4c858' }
};
var WALLS3 = {
  par_creme: { l: '#f0e4c8', r: '#d8ccb0' }, par_cinza: { l: '#8a8e98', r: '#70747e' }, par_laranja: { l: '#e8884a', r: '#c87238' }, par_vermelha: { l: '#b83a3a', r: '#982e2e' },
  par_branca: { l: '#f4f4f6', r: '#d8d8de' }, par_preta: { l: '#2a2a32', r: '#1e1e26' }, par_lilas: { l: '#a888d8', r: '#8e72bc' }, par_amarela: { l: '#f0d050', r: '#d8b840' },
  par_madeira: { l: '#a8702e', r: '#8a5a22', plank: 1 }, par_pedra: { l: '#8a8f98', r: '#70757e', brick: 1 }, par_celeste: { l: '#8fc4f0', r: '#74a8d8' },
  par_listras: { l: '#f0b8d0', r: '#d898b8', stripe: '#fff' }, par_listras2: { l: '#7ab0e8', r: '#6298d0', stripe: '#fff' }
};

const GROUPS_OLD = {"sala": ["sofa", "poltrona", "pufe", "mesinha", "tv", "estante", "caixa", "abajur", "vaso", "aquario", "tapete1", "tapete2", "tapete3"], "quarto": ["cama", "guarda_roupa"], "cozinha": ["mesa", "cadeira", "fogao", "pia", "geladeira"], "banheiro": ["privada", "banheira", "lavatorio", "chuveiro"], "escritorio": ["computador"], "jardim": ["arvore_j", "canteiro", "banco_j", "churrasqueira", "poste", "cerca", "piscina"], "lazer": ["fliper", "juke", "bau", "trofeu"], "decor": ["quadro1", "quadro2", "quadro3", "relogio", "neon", "prateleira", "espelho"]};
CAT3.forEach(function (r) { const o = { id: r[0], n: r[1], cat: r[2], p: r[3], w: r[4], d: r[5], g: r[7] }; if (r[8].indexOf('f') >= 0) o.flat = true; if (r[8].indexOf('w') >= 0) o.wall = true; if (r[8].indexOf('x') >= 0) o.x = 1; CAT.push(o); });
const CATMAP = {};
CAT.forEach(function (it) { CATMAP[it.id] = it; });
Object.keys(GROUPS_OLD).forEach(function (g) { GROUPS_OLD[g].forEach(function (id) { if (CATMAP[id]) CATMAP[id].g = g; }); });
const PLANS = {
  p: { id: 'p', n: 'Casa pequena', W: 14, H: 12, iw: 9, ih: 6,
    parts: [[5, 0, 1, 2], [5, 3, 1, 3], [6, 3, 1, 1], [8, 3, 1, 1]],
    zones: [{ id: 'sala', n: 'Sala', x: 0, y: 0, w: 5, h: 6 }, { id: 'quarto', n: 'Quarto', x: 6, y: 0, w: 3, h: 3 }, { id: 'banheiro', n: 'Banheiro', x: 6, y: 4, w: 3, h: 2 }],
    exit: [6, 11, 2, 1], spawn: [7, 10] },
  m: { id: 'm', n: 'Casa média', W: 17, H: 15, iw: 13, ih: 8,
    parts: [[6, 0, 1, 3], [6, 4, 1, 4], [7, 4, 1, 1], [9, 4, 4, 1], [10, 5, 1, 1], [10, 7, 1, 1]],
    zones: [{ id: 'sala', n: 'Sala', x: 0, y: 0, w: 6, h: 8 }, { id: 'quarto', n: 'Quarto', x: 7, y: 0, w: 6, h: 4 }, { id: 'cozinha', n: 'Cozinha', x: 7, y: 5, w: 3, h: 3 }, { id: 'banheiro', n: 'Banheiro', x: 11, y: 5, w: 2, h: 3 }],
    exit: [7, 14, 2, 1], spawn: [8, 13] },
  g: { id: 'g', n: 'Casa grande', W: 19, H: 17, iw: 15, ih: 9,
    parts: [[7, 0, 1, 3], [7, 4, 1, 3], [7, 8, 1, 1], [11, 0, 1, 1], [11, 2, 1, 2], [8, 4, 1, 1], [10, 4, 3, 1], [14, 4, 1, 1], [11, 5, 1, 1], [11, 7, 1, 2]],
    zones: [{ id: 'sala', n: 'Sala', x: 0, y: 0, w: 7, h: 9 }, { id: 'cozinha', n: 'Cozinha', x: 8, y: 0, w: 3, h: 4 }, { id: 'quarto', n: 'Quarto', x: 12, y: 0, w: 3, h: 4 }, { id: 'escritorio', n: 'Escritório', x: 8, y: 5, w: 3, h: 4 }, { id: 'banheiro', n: 'Banheiro', x: 12, y: 5, w: 3, h: 4 }],
    exit: [8, 16, 2, 1], spawn: [9, 15] }
};
Object.keys(PLANS).forEach(function (k) {
  const pl = PLANS[k]; pl.blocked = {};
  pl.parts.forEach(function (r) { for (let y = r[1]; y < r[1] + r[3]; y++) for (let x = r[0]; x < r[0] + r[2]; x++) pl.blocked[x + ',' + y] = 1; });
  for (let x = pl.exit[0]; x < pl.exit[0] + pl.exit[2]; x++) for (let y = pl.exit[1]; y < pl.exit[1] + pl.exit[3]; y++) pl.blocked[x + ',' + y] = 1;
});
const OWN_MAX = 8, HOUSE_MAX_ITEMS = 240;
const EXTRA_IDS = ['fliper', 'juke', 'trofeu', 'aquario', 'piso_galaxia', 'par_estrelas', 'pet_dragao', 'pet_raposa', 'pet_robo', 'piscina', 'neon'];
EXTRA_IDS.forEach(function (id) { if (CATMAP[id]) CATMAP[id].x = 1; });
const CAT_PUB = CAT.map(function (it) { const o = { id: it.id, n: it.n, cat: it.cat, p: it.p, w: it.w, d: it.d, g: it.g || '' }; if (it.flat) o.flat = 1; if (it.wall) o.wall = 1; if (it.ev) o.ev = it.ev; if (it.free) o.free = 1; if (it.x) o.x = 1; return o; });
/* moedas iniciais: cobrem uma unidade de tudo que é básico (sem itens de temporada nem extras), com folga */
const STARTER = Math.ceil(CAT.filter(function (it) { return !it.free && !it.ev && !it.x; }).reduce(function (s, it) { return s + it.p; }, 0) * 1.15 / 100) * 100;
const STARTER_OLD = 3900;
const EASY = 2;   /* multiplicador geral de moedas ganhas nas partidas */

function itemPrice(it) { if (it.free) return 0; return Math.max(1, Math.round(it.p * (1 - evSale()))); }
function itemOnShelf(it) { if (!it.ev) return true; const ev = EVENTS.find(function (e) { return e.id === it.ev; }); return !!ev && evActive(ev, true); }

/* ===== Fase 4: casa livre (terreno com paredes finas, portas e piso por tile) ===== */
const LOT_W = 22, LOT_H = 20, EXIT_X = 10, EXIT_Y = 19, WALL_MAX = 420, B36 = '0123456789abcdefghijklmnopqrstuvwxyz';
function lotCell(g, x, y) { return x >= 0 && y >= 0 && x < LOT_W && y < LOT_H && (g.fl[y].charAt(x) !== '.' || g.wl[y].charAt(x) !== '.'); }
function lotTall(g, x, y) { return !lotCell(g, x, y - 1) || !lotCell(g, x - 1, y); }
function isExitTile(x, y) { return y === EXIT_Y && x >= EXIT_X && x < EXIT_X + 2; }
function zoneAtP(pl, x, y) { for (let i = 0; i < pl.zones.length; i++) { const z = pl.zones[i]; if (x >= z.x && x < z.x + z.w && y >= z.y && y < z.y + z.h) return z; } return null; }
function zoneNearP(pl, x, y) {
  let z = zoneAtP(pl, x, y); if (z) return z;
  for (let r = 1; r < 5; r++) for (let dy = -r; dy <= r; dy++) for (let dx = -r; dx <= r; dx++) { z = zoneAtP(pl, x + dx, y + dy); if (z) return z; }
  return pl.zones[0];
}
/* converte uma planta antiga (e seus pisos/paredes por cômodo) para o terreno livre */
function plan2house(pid, flz, wlz, putOld) {
  const pl = PLANS[pid] || PLANS.m, OX = 3, OY = 2, fl = [], wl = [], fp = [], wp = [];
  for (let y = 0; y < LOT_H; y++) { fl.push(new Array(LOT_W).fill('.')); wl.push(new Array(LOT_W).fill('.')); }
  function fi(id) { let i = fp.indexOf(id); if (i < 0) { fp.push(id); i = fp.length - 1; } return B36.charAt(i); }
  function wi(id) { let i = wp.indexOf(id); if (i < 0) { wp.push(id); i = wp.length - 1; } return String.fromCharCode(97 + i); }
  flz = flz || {}; wlz = wlz || {};
  for (let y = 0; y < pl.ih; y++) for (let x = 0; x < pl.iw; x++) fl[OY + y][OX + x] = fi(flz[zoneNearP(pl, x, y).id] || 'piso_xadrez');
  function wid(x, y) { return wlz[zoneNearP(pl, Math.max(0, Math.min(pl.iw - 1, x)), Math.max(0, Math.min(pl.ih - 1, y))).id] || 'par_roxa'; }
  for (let y = -1; y <= pl.ih; y++) for (let x = -1; x <= pl.iw; x++) if (x === -1 || y === -1 || x === pl.iw || y === pl.ih) wl[OY + y][OX + x] = wi(wid(x, y));
  pl.parts.forEach(function (r) { for (let y = r[1]; y < r[1] + r[3]; y++) for (let x = r[0]; x < r[0] + r[2]; x++) wl[OY + y][OX + x] = wi(wid(x, y)); });
  /* porta da frente, na altura da saída antiga, e portas nos vãos entre paredes */
  const dx = OX + pl.exit[0];
  wl[OY + pl.ih][dx] = wl[OY + pl.ih][dx].toUpperCase();
  for (let y = 0; y < pl.ih; y++) for (let x = 0; x < pl.iw; x++) {
    if (wl[OY + y][OX + x] !== '.') continue;
    const w = wl[OY + y][OX + x - 1] !== '.' && wl[OY + y][OX + x + 1] !== '.', n = wl[OY + y - 1][OX + x] !== '.' && wl[OY + y + 1][OX + x] !== '.';
    if (w || n) wl[OY + y][OX + x] = wi(wid(x, y)).toUpperCase();
  }
  const put = [];
  (putOld || []).forEach(function (q) {
    if (!q || typeof q.id !== 'string') return;
    if (q.s === 'R') put.push({ id: q.id, s: 'S', x: OX + (q.i | 0), y: OY - 1, c: 0 });
    else if (q.s === 'L') put.push({ id: q.id, s: 'E', x: OX - 1, y: OY + (q.i | 0), c: 0 });
    else { const x = q.x | 0, y = q.y | 0; put.push({ id: q.id, x: x + OX + (x >= pl.iw ? 1 : 0), y: y + OY + (y >= pl.ih ? 1 : 0), r: q.r ? 1 : 0, c: 0 }); }
  });
  return { v: 2, fp: fp, wp: wp, fl: fl.map(function (r) { return r.join(''); }), wl: wl.map(function (r) { return r.join(''); }), put: put };
}
function cleanPut2(own, g, list) {
  const put = [], count = {}, taken = {}, flatTaken = {}, wallTaken = {};
  list = Array.isArray(list) ? list.slice(0, HOUSE_MAX_ITEMS) : [];
  for (let i = 0; i < list.length; i++) {
    const q = list[i], it = q && CATMAP[q.id];
    if (!it || ['movel', 'tapete', 'quadro'].indexOf(it.cat) === -1) continue;
    if ((count[it.id] || 0) >= (own[it.id] || 0)) continue;
    const c = (q.c | 0) & 15;
    if (it.wall) {
      const s = q.s === 'E' ? 'E' : 'S', x = q.x | 0, y = q.y | 0, k = s + x + ',' + y;
      if (x < 0 || y < 0 || x >= LOT_W || y >= LOT_H || wallTaken[k]) continue;
      const ch = g.wl[y].charAt(x);
      if (ch === '.' || ch !== ch.toLowerCase()) continue;
      const fx = s === 'S' ? x : x + 1, fy = s === 'S' ? y + 1 : y;
      if (fx >= LOT_W || fy >= LOT_H || g.fl[fy].charAt(fx) === '.' || !lotTall(g, x, y)) continue;
      wallTaken[k] = 1; count[it.id] = (count[it.id] || 0) + 1;
      put.push({ id: it.id, s: s, x: x, y: y, c: c });
    } else {
      const r = q.r ? 1 : 0, fw = r ? it.d : it.w, fd = r ? it.w : it.d, x = q.x | 0, y = q.y | 0;
      if (x < 0 || y < 0 || x + fw > LOT_W || y + fd > LOT_H) continue;
      const bag = it.flat ? flatTaken : taken;
      let clash = false;
      for (let yy = y; yy < y + fd && !clash; yy++) for (let xx = x; xx < x + fw; xx++) if (bag[xx + ',' + yy] || g.wl[yy].charAt(xx) !== '.' || isExitTile(xx, yy)) { clash = true; break; }
      if (clash) continue;
      for (let yy = y; yy < y + fd; yy++) for (let xx = x; xx < x + fw; xx++) bag[xx + ',' + yy] = 1;
      count[it.id] = (count[it.id] || 0) + 1;
      put.push({ id: it.id, x: x, y: y, r: r, c: c });
    }
  }
  return put;
}
function houseBase(a, m) {
  const own = a.items.own, fpIn = Array.isArray(m.fp) ? m.fp.slice(0, 36) : [], wpIn = Array.isArray(m.wp) ? m.wp.slice(0, 26) : [];
  const flIn = Array.isArray(m.fl) ? m.fl : [], wlIn = Array.isArray(m.wl) ? m.wl : [], fp = [], wp = [], fl = [], wl = [];
  let nWalls = 0;
  function okF(id) { return typeof id === 'string' && !!CATMAP[id] && CATMAP[id].cat === 'piso' && ownedOk(a, id); }
  function okW(id) { return typeof id === 'string' && !!CATMAP[id] && CATMAP[id].cat === 'parede' && ownedOk(a, id); }
  for (let y = 0; y < LOT_H; y++) {
    const rf = String(flIn[y] || ''), rw = String(wlIn[y] || '');
    let of = '', ow = '';
    for (let x = 0; x < LOT_W; x++) {
      let f = '.', w = '.';
      const cf = rf.charAt(x) || '.', cw = rw.charAt(x) || '.';
      if (cf !== '.') { const ix = parseInt(cf, 36); if (isFinite(ix) && ix < fpIn.length && okF(fpIn[ix])) { let j = fp.indexOf(fpIn[ix]); if (j < 0) { fp.push(fpIn[ix]); j = fp.length - 1; } f = B36.charAt(j); } }
      if (cw !== '.' && !isExitTile(x, y) && nWalls < WALL_MAX) {
        const lc = cw.toLowerCase(), wi = lc.charCodeAt(0) - 97;
        if (wi >= 0 && wi < wpIn.length && okW(wpIn[wi])) { let j = wp.indexOf(wpIn[wi]); if (j < 0) { wp.push(wpIn[wi]); j = wp.length - 1; } w = String.fromCharCode(97 + j); if (cw !== lc) w = w.toUpperCase(); nWalls++; }
      }
      of += f; ow += w;
    }
    fl.push(of); wl.push(ow);
  }
  return { v: 2, fp: fp, wp: wp, fl: fl, wl: wl, put: [] };
}

function cleanPut(own, pl, list) {
  const put = [], count = {}, taken = {}, flatTaken = {}, wallTaken = {};
  list = Array.isArray(list) ? list.slice(0, HOUSE_MAX_ITEMS) : [];
  for (let i = 0; i < list.length; i++) {
    const q = list[i], it = q && CATMAP[q.id];
    if (!it || ['movel', 'tapete', 'quadro'].indexOf(it.cat) === -1) continue;
    if ((count[it.id] || 0) >= (own[it.id] || 0)) continue;
    if (it.wall) {
      const s = q.s === 'R' ? 'R' : 'L', ix = q.i | 0, k = s + ix, lim = s === 'L' ? pl.ih : pl.iw;
      if (ix < 0 || ix >= lim || wallTaken[k]) continue;
      wallTaken[k] = 1; count[it.id] = (count[it.id] || 0) + 1;
      put.push({ id: it.id, s: s, i: ix });
    } else {
      const r = q.r ? 1 : 0, fw = r ? it.d : it.w, fd = r ? it.w : it.d, x = q.x | 0, y = q.y | 0;
      if (x < 0 || y < 0 || x + fw > pl.W || y + fd > pl.H) continue;
      const bag = it.flat ? flatTaken : taken;
      let clash = false;
      for (let yy = y; yy < y + fd && !clash; yy++) for (let xx = x; xx < x + fw; xx++) if (bag[xx + ',' + yy] || pl.blocked[xx + ',' + yy]) { clash = true; break; }
      if (clash) continue;
      for (let yy = y; yy < y + fd; yy++) for (let xx = x; xx < x + fw; xx++) bag[xx + ',' + yy] = 1;
      count[it.id] = (count[it.id] || 0) + 1;
      put.push({ id: it.id, x: x, y: y, r: r });
    }
  }
  return put;
}
function normItems(a) {
  const it = a.items && typeof a.items === 'object' ? a.items : {};
  it.own = it.own && typeof it.own === 'object' ? it.own : {};
  let h = it.house && typeof it.house === 'object' ? it.house : null;
  if (!h) {
    const r = it.room && typeof it.room === 'object' ? it.room : {};
    const fl = CATMAP[r.floor] && CATMAP[r.floor].cat === 'piso' ? r.floor : '', wl = CATMAP[r.wall] && CATMAP[r.wall].cat === 'parede' ? r.wall : '';
    const fz = {}, wz = {};
    PLANS.p.zones.forEach(function (z) { if (fl) fz[z.id] = fl; if (wl) wz[z.id] = wl; });
    h = plan2house('p', fz, wz, it.room && Array.isArray(r.put) ? cleanPut(it.own, PLANS.m, r.put) : []);
  } else if (h.v !== 2) {
    h = plan2house(PLANS[h.plan] ? h.plan : 'm', h.fl && typeof h.fl === 'object' ? h.fl : {}, h.wl && typeof h.wl === 'object' ? h.wl : {}, Array.isArray(h.put) ? h.put : []);
  }
  h.fp = Array.isArray(h.fp) ? h.fp : []; h.wp = Array.isArray(h.wp) ? h.wp : [];
  h.fl = Array.isArray(h.fl) && h.fl.length === LOT_H ? h.fl : plan2house('p').fl;
  h.wl = Array.isArray(h.wl) && h.wl.length === LOT_H ? h.wl : plan2house('p').wl;
  h.put = cleanPut2(it.own, h, Array.isArray(h.put) ? h.put : []);
  it.house = h; delete it.room;
  it.pet = typeof it.pet === 'string' && CATMAP[it.pet] && CATMAP[it.pet].cat === 'pet' ? it.pet : '';
  it.likes = it.likes && typeof it.likes === 'object' ? it.likes : {};
  it.visits = it.visits && typeof it.visits === 'object' ? it.visits : {};
  it.starter = it.starter ? 1 : 0; it.starter2 = it.starter2 ? 1 : 0;
  it.gal = Object.assign({ d: '', n: 0, total: 0, likes: 0 }, it.gal && typeof it.gal === 'object' ? it.gal : {});
  a.items = it;
  return it;
}
function itemsPub(a) {
  const it = a.items;
  return { own: it.own, house: it.house, pet: it.pet, likes: Object.keys(it.likes).length, visits: Object.keys(it.visits).length, gal: { total: it.gal.total, likes: it.gal.likes, d: it.gal.d, n: it.gal.n } };
}
function ownedOk(a, id) { const it = CATMAP[id]; return !!it && (it.free || (a.items.own[id] || 0) > 0); }

// valida e limpa a casa enviada pelo cliente; devolve { house, pet } ou { err }
function cleanHouse(a, m) {
  if (!m || typeof m !== 'object') return { err: 'Casa inválida.' };
  const base = houseBase(a, m);
  base.put = cleanPut2(a.items.own, base, m.put);
  const pet = m.pet === '' ? '' : (typeof m.pet === 'string' && CATMAP[m.pet] && CATMAP[m.pet].cat === 'pet' && (a.items.own[m.pet] || 0) > 0 ? m.pet : a.items.pet);
  return { house: base, pet: pet };
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
    const hh = it.house || it.room, put = hh && Array.isArray(hh.put) ? hh.put.length : 0;
    let pln = 'm';
    if (hh && hh.v === 2 && Array.isArray(hh.fl)) { const t = hh.fl.join('').replace(/\./g, '').length; pln = t < 70 ? 'p' : t < 130 ? 'm' : 'g'; } else if (hh && PLANS[hh.plan]) pln = hh.plan;
    const likes = it.likes && typeof it.likes === 'object' ? Object.keys(it.likes).length : 0;
    return { key: r.key, nick: a ? a.nick : r.nick, av: r.av || '', lv: lvOf(a ? a.xp : (r.xp | 0)), n: put, likes: likes, plan: pln };
  });
  out.sort(function (x, y) { return (y.likes - x.likes) || (y.n - x.n) || (y.lv - x.lv); });
  roomsCache = { t: Date.now(), v: out };
  return out;
}
function roomsOnline(list) {
  return list.map(function (r) { const m = playerByKey(r.key); return { nick: r.nick, av: r.av, lv: r.lv, n: r.n, likes: r.likes, plan: r.plan, on: !!(m && m.online) }; });
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
function boosted(coins) { return Math.round(coins * evMult() * EASY); }

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
      giveStarter(p);
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

  socket.on('scene', async function (m) {
    try {
      const p = playerOf(socket);
      if (!p || p.id !== socket.id || !m || room.phase !== 'lobby') return;
      const sc = String(m.sc || '');
      let ok = /^(arcade|praca|rua|parque)$/.test(sc);
      if (!ok && sc.indexOf('casa:') === 0) { const k = sc.slice(5); ok = k.length > 0 && k.length <= 40 && !!(await loadAcct(k)); }
      if (!ok) return;
      const x = Math.floor(Number(m.x)), y = Math.floor(Number(m.y));
      if (!(x >= 0 && x < 48 && y >= 0 && y < 48)) return;
      p.sc = sc;
      if (sc === 'arcade' && (isBlocked(x, y) || spotTaken(x, y, p))) { const t = freeTile(); p.x = t.x; p.y = t.y; } else { p.x = x; p.y = y; }
      sendPlayers();
    } catch (e) { console.error('scene', e); }
  });
  socket.on('walk', function (m) {
    try {
      const p = playerOf(socket);
      if (!p || room.phase !== 'lobby' || !m) return;
      const now = Date.now();
      if (now - p.lastWalk < 120) return;
      p.lastWalk = now;
      const x = Math.floor(Number(m.x)), y = Math.floor(Number(m.y));
      const arc = !p.sc || p.sc === 'arcade';
      if (arc ? (!(x >= 0 && x < ROOM_W && y >= 0 && y < ROOM_H) || isBlocked(x, y)) : !(x >= 0 && x < 48 && y >= 0 && y < 48)) return;
      if (arc && spotTaken(x, y, p)) { socket.emit('walk_no', { x: p.x, y: p.y }); return; }
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
      const a = p.acct, r = cleanHouse(a, m);
      if (r.err) { socket.emit('room_err', { msg: r.err }); return; }
      const petChanged = a.items.pet !== r.pet;
      a.items.house = r.house; a.items.pet = r.pet;
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
      socket.emit('room_data', { nick: a.nick || key, av: a.av || '', lv: lvOf(a.xp), house: a.items.house, pet: a.items.pet, likes: Object.keys(a.items.likes).length, liked: !!a.items.likes[p.key], mine: mine });
      if (!mine) {
        const today = dayKey();
        if (p.acct.items.visits[key] !== today) {
          if (p.acct.items.visits[key] || Object.keys(p.acct.items.visits).length < 200) p.acct.items.visits[key] = today;
          saveAcct(p);
          grant(p, { kind: 'visit', coins: 10, xp: 4, nick: a.nick || key });
          const owner = await mutateAcct(key, function (o) { o.coins += 5; o.total_coins += 5; });
          if (owner) grant(owner, { kind: 'visited', coins: 0, xp: 2, by: p.nick });
        }
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
      const owner = await mutateAcct(key, function (a) { a.items.likes[p.key] = 1; a.coins += 5; a.total_coins += 5; });
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
      grant(p, { kind: 'gal', coins: 10, xp: 10 });
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
      const owner = await mutateAcct(row.key, function (a) { a.coins += 3; a.total_coins += 3; a.items.gal.likes += 1; });
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
