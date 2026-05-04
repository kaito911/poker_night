const express = require('express');
const http = require('http');
const WebSocket = require('ws');
const path = require('path');

const app = express();
const server = http.createServer(app);
const wss = new WebSocket.Server({ server });

app.use(express.static(path.join(__dirname, 'public')));

const rooms = {};
const clientToRoom = new Map();
let clientIdCounter = 0;

// ─── Deck ───────────────────────────────────────────────────────────────────

const SUITS = ['♠', '♥', '♦', '♣'];
const VALUES = ['2','3','4','5','6','7','8','9','10','J','Q','K','A'];
const VALUE_RANK = Object.fromEntries(VALUES.map((v, i) => [v, i + 2]));

function createDeck() {
  const deck = [];
  for (const suit of SUITS) for (const value of VALUES) deck.push({ suit, value });
  for (let i = deck.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [deck[i], deck[j]] = [deck[j], deck[i]];
  }
  return deck;
}

// ─── Hand Evaluation ─────────────────────────────────────────────────────────

function cardValue(card) { return VALUE_RANK[card.value]; }

function getCombinations(arr, k) {
  if (k === 0) return [[]];
  if (arr.length < k) return [];
  const [h, ...t] = arr;
  return [...getCombinations(t, k - 1).map(c => [h, ...c]), ...getCombinations(t, k)];
}

function evaluate5(cards) {
  const vals = cards.map(cardValue).sort((a, b) => b - a);
  const suits = cards.map(c => c.suit);
  const isFlush = new Set(suits).size === 1;

  let isStraight = false;
  let straightHigh = vals[0];
  if (new Set(vals).size === 5 && vals[0] - vals[4] === 4) isStraight = true;
  if (JSON.stringify(vals) === JSON.stringify([14, 5, 4, 3, 2])) { isStraight = true; straightHigh = 5; }

  const freq = {};
  for (const v of vals) freq[v] = (freq[v] || 0) + 1;
  const groups = Object.entries(freq).sort((a, b) => b[1] - a[1] || b[0] - a[0]);
  const counts = groups.map(g => g[1]);
  const groupVals = groups.map(g => parseInt(g[0]));

  let rank, name;
  if (isFlush && isStraight && straightHigh === 14) { rank = 9; name = 'Royal Flush'; }
  else if (isFlush && isStraight) { rank = 8; name = 'Straight Flush'; }
  else if (counts[0] === 4) { rank = 7; name = 'Four of a Kind'; }
  else if (counts[0] === 3 && counts[1] === 2) { rank = 6; name = 'Full House'; }
  else if (isFlush) { rank = 5; name = 'Flush'; }
  else if (isStraight) { rank = 4; name = 'Straight'; }
  else if (counts[0] === 3) { rank = 3; name = 'Three of a Kind'; }
  else if (counts[0] === 2 && counts[1] === 2) { rank = 2; name = 'Two Pair'; }
  else if (counts[0] === 2) { rank = 1; name = 'Pair'; }
  else { rank = 0; name = 'High Card'; }

  return { rank, name, tiebreakers: isStraight ? [straightHigh] : groupVals };
}

function compareHands(a, b) {
  if (a.rank !== b.rank) return a.rank - b.rank;
  for (let i = 0; i < 5; i++) {
    const d = (a.tiebreakers[i] || 0) - (b.tiebreakers[i] || 0);
    if (d !== 0) return d;
  }
  return 0;
}

function bestHand(holeCards, community) {
  const all = [...holeCards, ...community];
  if (all.length < 5) return { rank: -1, name: '?', tiebreakers: [] };
  let best = null;
  for (const combo of getCombinations(all, 5)) {
    const h = evaluate5(combo);
    if (!best || compareHands(h, best) > 0) best = h;
  }
  return best;
}

// ─── Room/Game ────────────────────────────────────────────────────────────────

function generateCode() {
  const chars = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
  let code;
  do { code = Array.from({ length: 4 }, () => chars[Math.floor(Math.random() * chars.length)]).join(''); }
  while (rooms[code]);
  return code;
}

function makePlayer(id, name) {
  return { id, name, chips: 1000, cards: [], bet: 0, folded: false, allIn: false, connected: true };
}

function createRoom(ws, name) {
  const code = generateCode();
  rooms[code] = {
    code, hostId: ws.clientId,
    players: [makePlayer(ws.clientId, name)],
    deck: [], communityCards: [], pot: 0,
    currentBet: 0, phase: 'waiting',
    currentPlayerIndex: 0, dealerIndex: 0,
    toActQueue: [],
    smallBlind: 10, bigBlind: 20,
    winners: [], handResults: null, lastAction: null
  };
  clientToRoom.set(ws.clientId, code);
  return code;
}

function joinRoom(ws, name, code) {
  const room = rooms[code];
  if (!room) return { error: 'ルームが見つかりません' };
  if (room.phase !== 'waiting') return { error: 'ゲームはすでに開始しています' };
  if (room.players.length >= 8) return { error: 'ルームが満員です (最大8人)' };
  if (room.players.find(p => p.id === ws.clientId)) return { error: 'すでに参加しています' };
  room.players.push(makePlayer(ws.clientId, name));
  clientToRoom.set(ws.clientId, code);
  return { success: true };
}

function canAct(p) { return !p.folded && !p.allIn; }

function buildActQueue(room, startIndex) {
  const n = room.players.length;
  const queue = [];
  for (let i = 0; i < n; i++) {
    const idx = (startIndex + i) % n;
    if (canAct(room.players[idx])) queue.push(idx);
  }
  return queue;
}

function startHand(roomCode) {
  const room = rooms[roomCode];
  if (!room || room.players.length < 2) return;

  room.phase = 'preflop';
  room.deck = createDeck();
  room.communityCards = [];
  room.pot = 0;
  room.currentBet = room.bigBlind;
  room.winners = [];
  room.handResults = null;
  room.lastAction = null;

  for (const p of room.players) {
    p.cards = [room.deck.pop(), room.deck.pop()];
    p.bet = 0; p.folded = false; p.allIn = false;
  }

  const n = room.players.length;
  const sbIdx = (room.dealerIndex + 1) % n;
  const bbIdx = (room.dealerIndex + 2) % n;

  const sb = room.players[sbIdx];
  const bb = room.players[bbIdx];

  const sbAmt = Math.min(room.smallBlind, sb.chips);
  sb.chips -= sbAmt; sb.bet = sbAmt;
  if (sb.chips === 0) sb.allIn = true;

  const bbAmt = Math.min(room.bigBlind, bb.chips);
  bb.chips -= bbAmt; bb.bet = bbAmt;
  if (bb.chips === 0) bb.allIn = true;

  room.pot = sbAmt + bbAmt;
  room.currentBet = bbAmt;

  // Pre-flop: action starts UTG, goes around to BB (BB can check)
  const utgIdx = (bbIdx + 1) % n;
  room.toActQueue = buildActQueue(room, utgIdx);
  room.currentPlayerIndex = room.toActQueue[0] ?? -1;
}

function handleAction(roomCode, playerId, action, amount) {
  const room = rooms[roomCode];
  if (!room || room.phase === 'waiting' || room.phase === 'showdown') return false;

  const playerIndex = room.players.findIndex(p => p.id === playerId);
  if (room.toActQueue[0] !== playerIndex) return false;

  const player = room.players[playerIndex];
  let actionDesc = '';

  if (action === 'fold') {
    player.folded = true;
    actionDesc = `${player.name} がフォールド`;
    room.toActQueue.shift();
  } else if (action === 'check') {
    if (player.bet < room.currentBet) return false;
    actionDesc = `${player.name} がチェック`;
    room.toActQueue.shift();
  } else if (action === 'call') {
    const callAmt = Math.min(room.currentBet - player.bet, player.chips);
    player.chips -= callAmt; room.pot += callAmt; player.bet += callAmt;
    if (player.chips === 0) player.allIn = true;
    actionDesc = `${player.name} がコール (${callAmt})`;
    room.toActQueue.shift();
  } else if (action === 'raise') {
    const totalBet = Math.min(amount, player.chips + player.bet);
    if (totalBet <= room.currentBet) return false;
    const additional = totalBet - player.bet;
    player.chips -= additional; room.pot += additional; player.bet = totalBet;
    room.currentBet = totalBet;
    if (player.chips === 0) player.allIn = true;
    actionDesc = `${player.name} がレイズ → ${totalBet}`;
    room.toActQueue = buildActQueue(room, (playerIndex + 1) % room.players.length)
      .filter(idx => idx !== playerIndex);
  } else if (action === 'allin') {
    const allInTotal = player.chips + player.bet;
    room.pot += player.chips; player.bet = allInTotal; player.chips = 0; player.allIn = true;
    actionDesc = `${player.name} がオールイン (${allInTotal})`;
    if (allInTotal > room.currentBet) {
      room.currentBet = allInTotal;
      room.toActQueue = buildActQueue(room, (playerIndex + 1) % room.players.length)
        .filter(idx => idx !== playerIndex);
    } else {
      room.toActQueue.shift();
    }
  } else {
    return false;
  }

  room.lastAction = actionDesc;

  const active = room.players.filter(p => !p.folded);
  if (active.length === 1) {
    active[0].chips += room.pot;
    room.pot = 0;
    room.phase = 'showdown';
    room.winners = [active[0].id];
    room.handResults = null;
    room.currentPlayerIndex = -1;
    return true;
  }

  // Trim queue (remove newly folded/allIn)
  room.toActQueue = room.toActQueue.filter(idx => canAct(room.players[idx]));

  if (room.toActQueue.length === 0) {
    advancePhase(room);
  } else {
    room.currentPlayerIndex = room.toActQueue[0];
  }

  return true;
}

function advancePhase(room) {
  for (const p of room.players) p.bet = 0;
  room.currentBet = 0;

  const phaseOrder = ['preflop', 'flop', 'turn', 'river', 'showdown'];
  const nextPhase = phaseOrder[phaseOrder.indexOf(room.phase) + 1] || 'showdown';
  room.phase = nextPhase;

  if (room.phase === 'flop') {
    room.communityCards = [room.deck.pop(), room.deck.pop(), room.deck.pop()];
  } else if (room.phase === 'turn' || room.phase === 'river') {
    room.communityCards.push(room.deck.pop());
  }

  if (room.phase === 'showdown') {
    while (room.communityCards.length < 5) room.communityCards.push(room.deck.pop());
    doShowdown(room);
    return;
  }

  const active = room.players.filter(p => !p.folded);
  const canBet = active.filter(p => !p.allIn);

  if (canBet.length <= 1) {
    // Everyone left is all-in, just deal cards
    advancePhase(room);
    return;
  }

  const startIdx = (room.dealerIndex + 1) % room.players.length;
  room.toActQueue = buildActQueue(room, startIdx);
  room.currentPlayerIndex = room.toActQueue[0] ?? -1;
}

function doShowdown(room) {
  const active = room.players.filter(p => !p.folded);
  const results = active.map(p => ({
    player: p,
    eval: bestHand(p.cards, room.communityCards)
  })).sort((a, b) => compareHands(b.eval, a.eval));

  const top = results[0].eval;
  const winners = results.filter(r => compareHands(r.eval, top) === 0).map(r => r.player);
  const share = Math.floor(room.pot / winners.length);
  const rem = room.pot - share * winners.length;
  winners.forEach((w, i) => { w.chips += share + (i === 0 ? rem : 0); });

  room.pot = 0;
  room.winners = winners.map(w => w.id);
  room.handResults = results.map(r => ({
    id: r.player.id,
    name: r.player.name,
    cards: r.player.cards,
    handName: r.eval.name
  }));
  room.currentPlayerIndex = -1;
}

function nextHand(roomCode) {
  const room = rooms[roomCode];
  if (!room || room.phase !== 'showdown') return;
  room.players = room.players.filter(p => p.chips > 0);
  if (room.players.length < 2) { room.phase = 'waiting'; return; }
  room.dealerIndex = (room.dealerIndex + 1) % room.players.length;
  startHand(roomCode);
}

// ─── Broadcast ────────────────────────────────────────────────────────────────

function getWsById(id) {
  return [...wss.clients].find(c => c.clientId === id && c.readyState === WebSocket.OPEN);
}

function broadcastState(roomCode) {
  const room = rooms[roomCode];
  if (!room) return;

  for (const player of room.players) {
    const ws = getWsById(player.id);
    if (!ws) continue;

    const state = {
      myId: player.id,
      isHost: room.hostId === player.id,
      code: room.code,
      phase: room.phase,
      communityCards: room.communityCards,
      pot: room.pot,
      currentBet: room.currentBet,
      currentPlayerIndex: room.currentPlayerIndex,
      dealerIndex: room.dealerIndex,
      smallBlind: room.smallBlind,
      bigBlind: room.bigBlind,
      toActCount: room.toActQueue.length,
      winners: room.winners,
      handResults: room.handResults,
      lastAction: room.lastAction,
      players: room.players.map((p, idx) => ({
        id: p.id,
        name: p.name,
        chips: p.chips,
        bet: p.bet,
        folded: p.folded,
        allIn: p.allIn,
        connected: p.connected,
        isDealer: idx === room.dealerIndex,
        isCurrent: idx === room.currentPlayerIndex,
        // Show cards: own cards always, others' cards only at showdown
        cards: (p.id === player.id || room.phase === 'showdown') ? p.cards : p.cards.map(() => null)
      }))
    };

    ws.send(JSON.stringify({ type: 'game_state', payload: state }));
  }
}

// ─── WebSocket ────────────────────────────────────────────────────────────────

wss.on('connection', (ws) => {
  ws.clientId = ++clientIdCounter;

  ws.on('message', (raw) => {
    let msg;
    try { msg = JSON.parse(raw.toString()); } catch { return; }
    const { type, payload = {} } = msg;
    const roomCode = clientToRoom.get(ws.clientId);

    switch (type) {
      case 'create_room': {
        if (roomCode) break;
        const name = (payload.name || 'Player').slice(0, 12);
        const code = createRoom(ws, name);
        ws.send(JSON.stringify({ type: 'room_created', payload: { code, playerId: ws.clientId } }));
        broadcastState(code);
        break;
      }
      case 'join_room': {
        if (roomCode) break;
        const name = (payload.name || 'Player').slice(0, 12);
        const code = payload.code?.toUpperCase();
        const result = joinRoom(ws, name, code);
        if (result.error) {
          ws.send(JSON.stringify({ type: 'error', payload: { message: result.error } }));
        } else {
          ws.send(JSON.stringify({ type: 'room_joined', payload: { code, playerId: ws.clientId } }));
          broadcastState(code);
        }
        break;
      }
      case 'start_game': {
        if (!roomCode) break;
        const room = rooms[roomCode];
        if (!room || room.hostId !== ws.clientId || room.phase !== 'waiting') break;
        if (room.players.length < 2) {
          ws.send(JSON.stringify({ type: 'error', payload: { message: '2人以上必要です' } }));
          break;
        }
        startHand(roomCode);
        broadcastState(roomCode);
        break;
      }
      case 'player_action': {
        if (!roomCode) break;
        const ok = handleAction(roomCode, ws.clientId, payload.action, payload.amount);
        if (ok) broadcastState(roomCode);
        break;
      }
      case 'next_hand': {
        if (!roomCode) break;
        nextHand(roomCode);
        broadcastState(roomCode);
        break;
      }
    }
  });

  ws.on('close', () => {
    const roomCode = clientToRoom.get(ws.clientId);
    if (roomCode && rooms[roomCode]) {
      const room = rooms[roomCode];
      const player = room.players.find(p => p.id === ws.clientId);
      if (player) {
        player.connected = false;
        // Auto-fold if it's their turn
        if (room.toActQueue[0] === room.players.indexOf(player)) {
          handleAction(roomCode, ws.clientId, 'fold', 0);
        }
        broadcastState(roomCode);
      }
    }
    clientToRoom.delete(ws.clientId);
  });
});

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => {
  console.log(`🃏  Poker Night running → http://localhost:${PORT}`);
});
