'use strict';

/*
  Servidor do Gartic Listening.
  Sala única, até 25 jogadores. Tudo fica na memória: se o servidor reiniciar, a sala zera.

  Variável de ambiente opcional:
    ALLOWED_ORIGIN  endereço do site (ex.: https://seuusuario.github.io). Pode ter vários, separados por vírgula.
                    Sem ela, qualquer site pode conectar (útil para testar no seu computador).
*/

const http = require('http');
const { Server } = require('socket.io');

const PORT = Number(process.env.PORT) || 3000;
const MAX_PLAYERS = 25;
const GRACE_MS = 20000;   // tempo para quem caiu voltar com o mesmo apelido sem perder pontos
// Salão de fliperama: mesmo mapa do cliente (gerado a partir dele).
const HALL = {"W":22,"H":16,"blocked":[[3,0],[4,0],[6,0],[7,0],[9,0],[10,0],[12,0],[13,0],[18,0],[0,2],[21,2],[0,3],[16,3],[17,3],[0,4],[16,4],[17,4],[0,5],[0,6],[10,6],[11,6],[12,6],[0,7],[10,7],[11,7],[12,7],[0,8],[10,8],[11,8],[12,8],[0,9],[16,10],[17,10],[4,11],[5,11],[16,11],[17,11],[4,12],[5,12],[21,13],[2,15]],"spots":[[1,2,"pinball"],[1,3,"breakout"],[1,4,"cobrinha"],[1,5,"invasores"],[1,6,"blocos"],[1,7,"asteroides"],[1,8,"corrida"],[1,9,"memoria"],[3,1,"pong"],[4,1,"pong"],[6,1,"hoquei"],[7,1,"hoquei"],[9,1,"ligue4"],[10,1,"ligue4"],[12,1,"naval"],[13,1,"naval"],[9,6,"gartic"],[13,6,"gartic"],[9,7,"gartic"],[13,7,"gartic"],[9,8,"gartic"],[13,8,"gartic"],[9,9,"gartic"],[10,9,"gartic"],[11,9,"gartic"],[12,9,"gartic"],[13,9,"gartic"],[15,5,"quiz"],[16,5,"quiz"],[17,5,"quiz"],[18,5,"quiz"],[15,6,"quiz"],[16,6,"quiz"],[17,6,"quiz"],[18,6,"quiz"],[15,7,"quiz"],[16,7,"quiz"],[17,7,"quiz"],[18,7,"quiz"],[15,9,"batata"],[16,9,"batata"],[17,9,"batata"],[18,9,"batata"],[15,10,"batata"],[18,10,"batata"],[15,11,"batata"],[18,11,"batata"],[15,12,"batata"],[16,12,"batata"],[17,12,"batata"],[18,12,"batata"],[3,10,"arena"],[4,10,"arena"],[5,10,"arena"],[6,10,"arena"],[3,11,"arena"],[6,11,"arena"],[3,12,"arena"],[6,12,"arena"],[3,13,"arena"],[4,13,"arena"],[5,13,"arena"],[6,13,"arena"],[18,1,"jukebox"]],"spawn":[[8,12],[9,12],[10,12],[11,12],[12,12],[13,12],[8,13],[9,13],[10,13],[11,13],[12,13],[13,13],[8,14],[9,14],[10,14],[11,14],[12,14],[13,14],[8,15],[9,15],[10,15],[11,15],[12,15],[13,15]]};
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

const server = http.createServer(function (req, res) {
  const url = (req.url || '/').split('?')[0];
  if (url === '/' || url === '/health') {
    res.writeHead(200, { 'Content-Type': 'text/plain; charset=utf-8', 'Cache-Control': 'no-store' });
    res.end('Servidor do Gartic Listening no ar. Jogadores conectados: ' + onlinePlayers().length + ' de ' + MAX_PLAYERS + '.');
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
  socket.on('join', function (data) {
    try {
      if (socket.data.key) return;
      const nick = cleanNick(data && data.nick);
      const err = nickError(nick);
      if (err) { socket.emit('join_error', { msg: err }); return; }
      const key = nick.toLowerCase();
      const av = cleanAvatar(data && data.av);
      let p = playerByKey(key);
      let returning = false;
      if (p) {
        if (p.online) { socket.emit('join_error', { msg: 'Esse apelido já está em uso por alguém na sala.' }); return; }
        if (av && avatarTaken(av, key)) { socket.emit('join_error', { code: 'av', msg: 'Esse visual já está em uso por outra pessoa. Escolha outro.', taken: takenList() }); return; }
        if (p.offTimer) { clearTimeout(p.offTimer); p.offTimer = null; }
        if (av) p.av = av;
        p.id = socket.id;
        p.online = true;
        returning = true;
      } else {
        if (room.players.length >= MAX_PLAYERS) { socket.emit('join_error', { msg: 'A sala está cheia (' + MAX_PLAYERS + ' jogadores).' }); return; }
        if (av && avatarTaken(av, key)) { socket.emit('join_error', { code: 'av', msg: 'Esse visual já está em uso por outra pessoa. Escolha outro.', taken: takenList() }); return; }
        const t = freeTile();
        p = { nick: nick, key: key, av: av, x: t.x, y: t.y, stats: newStats(), lastReact: 0, lastSay: 0, lastWalk: 0, id: socket.id, online: true, score: 0, gain: 0, guessed: false, offTimer: null, lastMsg: 0 };
        room.players.push(p);
      }
      socket.data.key = key;
      socket.emit('joined', { nick: p.nick, av: p.av || '', players: publicPlayers(), phase: room.phase });
      sys(p.nick + (returning ? ' voltou.' : ' entrou.'));
      sendPlayers();
      sendStateTo(socket, p);
    } catch (e) { console.error('join', e); }
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
        q.duoWith = p.key; p.duoWith = q.key;
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

  socket.on('disconnect', function () {
    try {
      const p = playerOf(socket);
      if (!p || p.id !== socket.id) return;
      p.id = null;
      p.online = false;
      p.pl = '';
      duoLeave(p);
      p.offTimer = setTimeout(function () { removePlayer(p); }, GRACE_MS);
      if (room.phase === 'round' && room.drawer !== p.key && everyoneGuessed()) endRound('all');
      sendPlayers();
    } catch (e) { console.error('disconnect', e); }
  });
});

process.on('uncaughtException', function (e) { console.error('uncaughtException', e); });
process.on('unhandledRejection', function (e) { console.error('unhandledRejection', e); });

server.listen(PORT, function () {
  console.log('Servidor do Gartic Listening rodando na porta ' + PORT + '.');
  console.log(ALLOWED.length ? 'Aceitando conexões de: ' + ALLOWED.join(', ') : 'ALLOWED_ORIGIN vazio: aceitando conexões de qualquer site (modo de teste).');
});
