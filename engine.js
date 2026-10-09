/*
 * "Точки" (Dots) — game engine.
 *
 * Pure logic, no DOM. Works in the browser (attaches to window) and in Node
 * (attaches to globalThis), so the rules and the search can be tested.
 *
 * The board is infinite. Nodes are addressed by integer coordinates and stored
 * sparsely in Maps: `dots` holds the coloured dots and prisoners, `claimed`
 * holds every cell of a captured fortress (so nobody can play inside it).
 *
 * Capture rule
 * ------------
 * A player's active dot is a wall. Walls are 8-connected (a diagonal chain is
 * solid), while the region is explored 4-ways, so the connectivities are dual.
 * Since the walls are finite, any pocket lies in their bounding box; a flood
 * fill from the box border separates enclosed pockets from infinity. A pocket
 * is captured only when it contains at least one active enemy dot.
 *
 * Computer opponent
 * -----------------
 * `bestMove` runs iterative-deepening alpha-beta (negamax with an explicit
 * maximizing/minimizing side, which handles the "extra move after a capture"
 * rule for free). It uses:
 *   - capture extensions and a quiescence search, so forced capture chains are
 *     followed past the horizon instead of being cut off mid-fight;
 *   - a transposition table, PVS, late-move reductions, and move ordering
 *     (captures first, then killer/history/proximity), so it reaches real depth
 *     within a tight time budget;
 *   - a positional evaluation distilled from A. Priymak's manual: material
 *     (prisoners), connected walls, group liberties ("freedom"), grounding on
 *     the board edge, encirclement pressure, and the enemy mass sitting in
 *     cramped groups one move from capture. This makes it build long walls, use
 *     space, attack weak groups and defend its own;
 *   - repetition detection, so a pointless loop is scored as a draw and the
 *     engine plays for progress.
 * The game has no terminal state (the board never fills, the loser can always
 * play on), so "play to the end" is impossible by definition; iterative
 * deepening plus the budget is the practical maximum.
 *
 * Weights live in the mutable `W` table and can be overridden at runtime with
 * `DotsEngine.setWeights({...})` (used by the self-play tuning harness).
 */
(function (root) {
	'use strict';

	var EMPTY = 0;
	var P1 = 1;
	var P2 = 2;
	var C1 = 3;
	var C2 = 4;

	var TIMEOUT = {};

	var now = (typeof performance !== 'undefined' && performance.now)
		? function () { return performance.now(); }
		: function () { return Date.now(); };

	/*
	 * Node keys. Coordinates are packed into a single integer so that the Maps
	 * and Sets the engine is built on use numeric keys: no string building and
	 * no parsing in the hot paths. The offset allows negative coordinates on the
	 * endless board; coordinates stay far inside the supported range in practice.
	 */
	var KEY_OFF = 1 << 20;
	var KEY_MUL = 1 << 21;

	function key(x, y) { return (x + KEY_OFF) * KEY_MUL + (y + KEY_OFF); }
	function parseKey(k) {
		var t = k % KEY_MUL;
		return [(k - t) / KEY_MUL - KEY_OFF, t - KEY_OFF];
	}

	function other(player) { return player === P1 ? P2 : P1; }
	function isActive(v) { return v === P1 || v === P2; }
	function isPrisoner(v) { return v === C1 || v === C2; }
	function ownerOf(v) {
		if (v === P1 || v === C1) return P1;
		if (v === P2 || v === C2) return P2;
		return 0;
	}
	function prisonerValue(player) { return player === P1 ? C1 : C2; }

	/* ---- position hashing (Zobrist-style, computed on the fly) ------------ */

	var TT_EXACT = 0, TT_LOWER = 1, TT_UPPER = 2;
	var HASH_SALT_A = 0x5bd1e995, HASH_SALT_B = 0x27d4eb2f;
	var HASH_DOT = 0, HASH_CLAIMED = 16;

	function zobValue(x, y, v, salt) {
		if (!v) return 0;
		var h = (Math.imul(x, 0x9E3779B1) ^ Math.imul(y, 0x85EBCA77) ^ Math.imul(v, 0xC2B2AE3D) ^ salt) | 0;
		h ^= h >>> 15; h = Math.imul(h, 0x2C1B3C6D);
		h ^= h >>> 12; h = Math.imul(h, 0x297A2D39);
		h ^= h >>> 15;
		return h | 0;
	}

	function hashDelta(k, kindBase, oldV, newV) {
		var p = parseKey(k);
		var o = (oldV || 0) ? kindBase + oldV : 0;
		var n = (newV || 0) ? kindBase + newV : 0;
		return [
			zobValue(p[0], p[1], o, HASH_SALT_A) ^ zobValue(p[0], p[1], n, HASH_SALT_A),
			zobValue(p[0], p[1], o, HASH_SALT_B) ^ zobValue(p[0], p[1], n, HASH_SALT_B)
		];
	}

	function positionKey(state) {
		return state.h1 + ':' + state.h2 + ':' + state.turn;
	}

	function createGame(options) {
		options = options || {};
		return {
			dots: new Map(),
			claimed: new Map(),
			turn: P1,
			score: { 1: 0, 2: 0 },
			rules: { extraTurn: options.extraTurn !== false },
			bounds: options.bounds
				? { x0: options.bounds.x0, y0: options.bounds.y0, x1: options.bounds.x1, y1: options.bounds.y1 }
				: null,
			h1: 0,
			h2: 0,
			lastMove: null,
			moveCount: 0
		};
	}

	function clone(state) {
		return {
			dots: new Map(state.dots),
			claimed: new Map(state.claimed),
			turn: state.turn,
			score: { 1: state.score[1], 2: state.score[2] },
			rules: { extraTurn: state.rules.extraTurn },
			bounds: state.bounds
				? { x0: state.bounds.x0, y0: state.bounds.y0, x1: state.bounds.x1, y1: state.bounds.y1 }
				: null,
			h1: state.h1 | 0,
			h2: state.h2 | 0,
			lastMove: state.lastMove
				? { x: state.lastMove.x, y: state.lastMove.y, player: state.lastMove.player }
				: null,
			moveCount: state.moveCount
		};
	}

	/* Inside the rectangular field, when the game has one. Infinite otherwise. */
	function inBounds(state, x, y) {
		var b = state.bounds;
		return !b || (x >= b.x0 && x <= b.x1 && y >= b.y0 && y <= b.y1);
	}

	function canPlace(state, x, y) {
		var k = key(x, y);
		if (state.dots.has(k) || state.claimed.has(k)) return false;
		return inBounds(state, x, y);
	}

	/*
	 * All enclosed regions of `owner` (walls = owner's active dots). Returns an
	 * array of components, each an array of [x, y] cells.
	 */
	function componentsFor(state, owner) {
		var walls = [];
		var minX = Infinity, maxX = -Infinity, minY = Infinity, maxY = -Infinity;
		state.dots.forEach(function (v, k) {
			if (v !== owner) return;
			var p = parseKey(k);
			var x = p[0], y = p[1];
			walls.push([x, y]);
			if (x < minX) minX = x;
			if (x > maxX) maxX = x;
			if (y < minY) minY = y;
			if (y > maxY) maxY = y;
		});
		if (!walls.length) return [];

		var x0 = minX - 1, y0 = minY - 1, x1 = maxX + 1, y1 = maxY + 1;
		var w = x1 - x0 + 1, h = y1 - y0 + 1, total = w * h;
		var wall = new Uint8Array(total);
		var i;
		for (i = 0; i < walls.length; i++) {
			wall[(walls[i][1] - y0) * w + (walls[i][0] - x0)] = 1;
		}

		var outside = new Uint8Array(total);
		var stack = [];
		function addOutside(idx) {
			if (!wall[idx] && !outside[idx]) {
				outside[idx] = 1;
				stack.push(idx);
			}
		}
		function seed(cx, cy) {
			if (cx < x0 || cx > x1 || cy < y0 || cy > y1) return;
			addOutside((cy - y0) * w + (cx - x0));
		}
		for (var cx = x0; cx <= x1; cx++) { seed(cx, y0); seed(cx, y1); }
		for (var cy = y0; cy <= y1; cy++) { seed(x0, cy); seed(x1, cy); }

		while (stack.length) {
			var idx = stack.pop();
			var gx = idx % w, gy = (idx / w) | 0;
			if (gx > 0) addOutside(idx - 1);
			if (gx < w - 1) addOutside(idx + 1);
			if (gy > 0) addOutside(idx - w);
			if (gy < h - 1) addOutside(idx + w);
		}

		var seen = new Uint8Array(total);
		var comps = [];
		for (var start = 0; start < total; start++) {
			if (wall[start] || outside[start] || seen[start]) continue;
			var comp = [];
			var q = [start];
			seen[start] = 1;
			while (q.length) {
				var cur = q.pop();
				var qx = cur % w, qy = (cur / w) | 0;
				comp.push([qx + x0, qy + y0]);
				if (qx > 0 && !seen[cur - 1] && !wall[cur - 1] && !outside[cur - 1]) { seen[cur - 1] = 1; q.push(cur - 1); }
				if (qx < w - 1 && !seen[cur + 1] && !wall[cur + 1] && !outside[cur + 1]) { seen[cur + 1] = 1; q.push(cur + 1); }
				if (qy > 0 && !seen[cur - w] && !wall[cur - w] && !outside[cur - w]) { seen[cur - w] = 1; q.push(cur - w); }
				if (qy < h - 1 && !seen[cur + w] && !wall[cur + w] && !outside[cur + w]) { seen[cur + w] = 1; q.push(cur + w); }
			}
			comps.push(comp);
		}
		return comps;
	}

	/*
	 * Apply a move and return an undo log. Used by place() and by the search,
	 * which makes and unmakes millions of moves.
	 */
	function applyMove(state, x, y) {
		var k0 = key(x, y);
		if (!canPlace(state, x, y)) return { ok: false };

		var player = state.turn;
		var foe = other(player);
		var log = {
			ok: true,
			player: player,
			dotChanges: [],
			claimedChanges: [],
			captured: [],
			prevTurn: state.turn,
			prevScore1: state.score[1],
			prevScore2: state.score[2],
			prevLast: state.lastMove,
			prevMoveCount: state.moveCount,
			capturedCount: 0,
			extraTurn: false
		};

		var d0 = hashDelta(k0, HASH_DOT, undefined, player);
		state.h1 ^= d0[0]; state.h2 ^= d0[1];
		state.dots.set(k0, player);
		log.dotChanges.push({ k: k0, old: undefined, hd: d0 });
		state.moveCount++;
		state.lastMove = { x: x, y: y, player: player };

		/*
		 * A capture requires the new dot to sit on a closed loop of the mover's
		 * walls, so it must touch at least two of the mover's own dots. Without
		 * that, no enclosure can be completed and the (expensive) flood fill is
		 * skipped entirely — a large speed-up, since most placed dots have fewer
		 * than two same-coloured neighbours.
		 */
		var same = 0;
		for (var sdx = -1; sdx <= 1; sdx++) {
			for (var sdy = -1; sdy <= 1; sdy++) {
				if (sdx === 0 && sdy === 0) continue;
				if (state.dots.get(key(x + sdx, y + sdy)) === player) same++;
			}
		}

		var i, j;
		if (same >= 2) {
			var comps = componentsFor(state, player);
			for (i = 0; i < comps.length; i++) {
				var comp = comps[i];
				var enemies = [];
				for (j = 0; j < comp.length; j++) {
					if (state.dots.get(key(comp[j][0], comp[j][1])) === foe) enemies.push(comp[j]);
				}
				if (!enemies.length) continue;
				for (j = 0; j < enemies.length; j++) {
					var ek = key(enemies[j][0], enemies[j][1]);
					var oldE = state.dots.get(ek);
					var nvE = prisonerValue(foe);
					var dE = hashDelta(ek, HASH_DOT, oldE, nvE);
					state.h1 ^= dE[0]; state.h2 ^= dE[1];
					log.dotChanges.push({ k: ek, old: oldE, hd: dE });
					state.dots.set(ek, nvE);
					log.captured.push({ x: enemies[j][0], y: enemies[j][1] });
				}
				for (j = 0; j < comp.length; j++) {
					var ck = key(comp[j][0], comp[j][1]);
					var oldC = state.claimed.get(ck);
					var dC = hashDelta(ck, HASH_CLAIMED, oldC, player);
					state.h1 ^= dC[0]; state.h2 ^= dC[1];
					log.claimedChanges.push({ k: ck, old: oldC, hd: dC });
					state.claimed.set(ck, player);
				}
			}
		}

		state.score[player] += log.captured.length;
		log.capturedCount = log.captured.length;
		log.extraTurn = log.capturedCount > 0 && state.rules.extraTurn;
		if (!log.extraTurn) state.turn = foe;
		return log;
	}

	function undoMove(state, log) {
		var i, c;
		for (i = log.dotChanges.length - 1; i >= 0; i--) {
			c = log.dotChanges[i];
			if (c.hd) { state.h1 ^= c.hd[0]; state.h2 ^= c.hd[1]; }
			if (c.old === undefined) state.dots.delete(c.k);
			else state.dots.set(c.k, c.old);
		}
		for (i = log.claimedChanges.length - 1; i >= 0; i--) {
			c = log.claimedChanges[i];
			if (c.hd) { state.h1 ^= c.hd[0]; state.h2 ^= c.hd[1]; }
			if (c.old === undefined) state.claimed.delete(c.k);
			else state.claimed.set(c.k, c.old);
		}
		state.score[1] = log.prevScore1;
		state.score[2] = log.prevScore2;
		state.turn = log.prevTurn;
		state.lastMove = log.prevLast;
		state.moveCount = log.prevMoveCount;
	}

	function place(state, x, y) {
		var log = applyMove(state, x, y);
		if (!log.ok) return { ok: false };
		var claimed = [];
		for (var i = 0; i < log.claimedChanges.length; i++) {
			var c = log.claimedChanges[i];
			if (c.old === undefined) {
				var p = parseKey(c.k);
				claimed.push({ x: p[0], y: p[1] });
			}
		}
		return {
			ok: true,
			player: log.player,
			captured: log.captured,
			capturedCount: log.capturedCount,
			claimed: claimed,
			extraTurn: log.extraTurn,
			gameOver: false
		};
	}

	function activeCount(state, player) {
		var n = 0;
		state.dots.forEach(function (v) { if (v === player) n++; });
		return n;
	}

	function prisonerCount(state, player) {
		var value = prisonerValue(player);
		var n = 0;
		state.dots.forEach(function (v) { if (v === value) n++; });
		return n;
	}

	function isGameOver() { return false; }

	/*
	 * Drop the opening dots straight onto the board (no turn bookkeeping, no
	 * capture resolution — a start position never encloses anything). Each cell
	 * is { x, y, player }.
	 */
	function seed(state, cells) {
		if (!cells) return state;
		for (var i = 0; i < cells.length; i++) {
			var c = cells[i];
			var p = c.player || c.p;
			if (p !== P1 && p !== P2) continue;
			var k = key(c.x, c.y);
			if (state.dots.has(k) || state.claimed.has(k)) continue;
			var d = hashDelta(k, HASH_DOT, undefined, p);
			state.h1 ^= d[0]; state.h2 ^= d[1];
			state.dots.set(k, p);
		}
		return state;
	}

	/*
	 * A player is "grounded" (заземлён) when every one of their 8-connected
	 * groups touches the board edge, so the whole wall is anchored and cannot be
	 * enclosed. Impossible on the endless board (there is no edge).
	 */
	function isGrounded(state, player) {
		var b = state.bounds;
		if (!b) return false;
		var visited = new Set();
		var any = false, all = true;
		state.dots.forEach(function (v, k0) {
			if (v !== player || visited.has(k0)) return;
			any = true;
			var stack = [k0];
			visited.add(k0);
			var touch = false;
			while (stack.length) {
				var ck = stack.pop();
				var p = parseKey(ck);
				if (p[0] === b.x0 || p[0] === b.x1 || p[1] === b.y0 || p[1] === b.y1) touch = true;
				for (var dx = -1; dx <= 1; dx++) {
					for (var dy = -1; dy <= 1; dy++) {
						if (dx === 0 && dy === 0) continue;
						var nk = key(p[0] + dx, p[1] + dy);
						if (state.dots.get(nk) === player && !visited.has(nk)) { visited.add(nk); stack.push(nk); }
					}
				}
			}
			if (!touch) all = false;
		});
		return any && all;
	}

	/* Is there at least one free point left to play? Always true when endless. */
	function hasAnyMove(state) {
		var b = state.bounds;
		if (!b) return true;
		for (var x = b.x0; x <= b.x1; x++) {
			for (var y = b.y0; y <= b.y1; y++) {
				if (canPlace(state, x, y)) return true;
			}
		}
		return false;
	}

	/* ==================================================================== AI */

	/*
	 * Positional knowledge for "Точки", distilled from A. Priymak's manual:
	 *
	 *   structure (walls)  — connected dots are the unit of play. A long,
	 *                        unbroken wall is strong; a lone, disconnected dot
	 *                        is worth little. We reward own-own adjacencies.
	 *   freedom (liberties)— a group with few reachable empty cells is cramped
	 *                        and can be enclosed. Captures are resolved by the
	 *                        search; the evaluation only has to rank the quiet
	 *                        positions that lead to them.
	 *   grounding          — a group touching the board edge cannot be enclosed
	 *                        (the region beyond the edge is not captured), so
	 *                        reaching the edge is valuable and attacking a
	 *                        grounded wall is pointless.
	 *   pressure           — crowding the enemy while staying connected attacks;
	 *                        the same crowding of my dots is a threat.
	 *   potential          — enemy mass sitting in a cramped, nearly enclosed
	 *                        group is the best thing to aim at; the mirror case
	 *                        (my own cramped mass) is the worst.
	 *
	 * Weights are tuned by self-play (see the benchmark harness).
	 */

	var W = {
		score: 100,    /* captured prisoners — the win condition */
		conn: 2.0,     /* own-own adjacencies (wall strength) */
		free: 1.7,     /* reachable escape cells */
		edge: 1.8,     /* dots grounded on the edge */
		press: 3.0,    /* enemy dots crowded by my groups */
		vuln: 6.0,     /* mass of a cramped enemy group (target) */
		vulnOwn: 1.0,  /* mass of a cramped own group (risk) */
		big: 1.5,      /* size of the largest connected wall */
		tight: 6.0,    /* count of cramped enemy groups */
		tightOwn: 1.0, /* count of cramped own groups */
		atari: 20,     /* enemy groups one move from capture */
		near: 6,       /* enemy groups two escapes from capture */
		gground: 4,    /* fully grounded enemy groups (hard to attack) */
		danger: 3      /* a group with fewer escapes than this is cramped */
	};

	function setWeights(o) { if (o) for (var k in o) if (W[k] !== undefined) W[k] = o[k]; }

	/*
	 * Aggregate structural features for both sides in one pass over the dots.
	 * A group is an 8-connected set of active dots of one player; `boundary` is
	 * the number of distinct reachable empty cells around it (its liberties);
	 * `contact` counts the enemy dots touching it.
	 */
	function analyzeBoth(state) {
		var bounds = state.bounds;
		var visited = new Set();
		var mark = new Map();
		var mark4 = new Map();
		var gid = 0;
		function blank() {
			return { size: 0, groups: 0, conn: 0, boundary: 0, contact: 0,
				grounded: 0, gground: 0, vuln: 0, big: 0, tight: 0, atari: 0, near: 0 };
		}
		var out = { 1: blank(), 2: blank() };

		state.dots.forEach(function (v, k0) {
			if ((v !== P1 && v !== P2) || visited.has(k0)) return;
			var player = v, foe = other(player);
			var R = out[player];
			var stack = [k0];
			visited.add(k0);
			gid++;
			var gsize = 0, gbound = 0, gorth = 0, gcontact = 0, gground = false;
			while (stack.length) {
				var ck = stack.pop();
				var p = parseKey(ck);
				var x = p[0], y = p[1];
				gsize++;
				if (bounds && (x === bounds.x0 || x === bounds.x1 || y === bounds.y0 || y === bounds.y1)) gground = true;
				for (var dx = -1; dx <= 1; dx++) {
					for (var dy = -1; dy <= 1; dy++) {
						if (dx === 0 && dy === 0) continue;
						var nk = key(x + dx, y + dy);
						var t = state.dots.get(nk);
						if (t === player) {
							R.conn++;
							if (!visited.has(nk)) { visited.add(nk); stack.push(nk); }
						} else if (t === undefined) {
							if (!state.claimed.has(nk)) {
								if (mark.get(nk) !== gid) { mark.set(nk, gid); gbound++; }
								/* orthogonal escapes are the ones a capture has to seal */
								if ((dx === 0 || dy === 0) && mark4.get(nk) !== gid) { mark4.set(nk, gid); gorth++; }
							}
						} else if (t === foe) {
							gcontact++;
						}
					}
				}
			}
			R.boundary += gbound;
			R.contact += gcontact;
			R.size += gsize;
			R.groups++;
			if (gground) { R.grounded += gsize; R.gground++; }
			if (gbound < W.danger) {
				R.tight++;
				R.vuln += gsize * (W.danger - gbound);
			}
			if (!gground) {
				if (gorth <= 1) R.atari++;
				else if (gorth === 2) R.near++;
			}
			if (gsize > R.big) R.big = gsize;
		});
		return out;
	}

	function evaluate(state, ai) {
		var r = analyzeBoth(state);
		var m = r[ai], o = r[other(ai)];
		var val = (state.score[ai] - state.score[other(ai)]) * W.score;
		val += (m.conn - o.conn) * W.conn;
		val += (m.boundary - o.boundary) * W.free;
		val += (m.grounded - o.grounded) * W.edge;
		val += (m.gground - o.gground) * W.gground;
		val += (m.contact - o.contact) * W.press;
		val += o.vuln * W.vuln - m.vuln * W.vulnOwn;
		val += (m.big - o.big) * W.big;
		val += o.tight * W.tight - m.tight * W.tightOwn;
		val += (o.atari - m.atari) * W.atari;
		val += (o.near - m.near) * W.near;
		return val;
	}

	/* ---- candidate offsets around a dot -------------------------------- */
	/* RING1: the 8 neighbours. RING2FULL: the 16 cells at Chebyshev distance
	   two. RING2AXIS: the 8 cells two steps out along an axis or diagonal,
	   which is how a wall or an abstract chain is stretched forward. */

	var RING1 = [], RING2FULL = [], RING2AXIS = [];
	(function () {
		for (var dx = -2; dx <= 2; dx++) {
			for (var dy = -2; dy <= 2; dy++) {
				if (dx === 0 && dy === 0) continue;
				var d = Math.max(Math.abs(dx), Math.abs(dy));
				if (d === 1) RING1.push([dx, dy]);
				else if (d === 2) {
					RING2FULL.push([dx, dy]);
					if (Math.abs(dx) === 2 && Math.abs(dy) === 2) RING2AXIS.push([dx, dy]);
					else if (dx === 0 || dy === 0) RING2AXIS.push([dx, dy]);
				}
			}
		}
	})();

	function orderScore(state, x, y, side, ctx, ply) {
		var score = 0;
		var foe = other(side);
		for (var dx = -1; dx <= 1; dx++) {
			for (var dy = -1; dy <= 1; dy++) {
				if (dx === 0 && dy === 0) continue;
				var t = state.dots.get(key(x + dx, y + dy));
				if (t === undefined || isPrisoner(t)) continue;
				if (t === foe) score += 6;
				else if (t === side) score += 3;
			}
		}
		var kk = key(x, y);
		var killers = ctx.killer[ply];
		if (killers) {
			if (killers[0] === kk) score += 60;
			else if (killers[1] === kk) score += 40;
		}
		score += (ctx.history[kk] || 0) * 0.01;
		return score;
	}

	/*
	 * Every move that captures right now. A capture needs an almost-closed wall
	 * around an enemy group, so only the free cells touching a cramped enemy dot
	 * are considered; each is verified by actually playing it. A finishing dot
	 * must touch at least two of the mover's own dots (it lies on the closing
	 * loop), which cheaply rejects the vast majority before the flood fill.
	 */
	function captureMoves(state, maxFree, limit) {
		var side = state.turn;
		var foe = other(side);
		var cand = new Set();
		state.dots.forEach(function (v, k) {
			if (v !== foe) return;
			var p = parseKey(k);
			var x = p[0], y = p[1];
			var free = 0, cells = [];
			for (var dx = -1; dx <= 1; dx++) {
				for (var dy = -1; dy <= 1; dy++) {
					if (dx === 0 && dy === 0) continue;
					var nx = x + dx, ny = y + dy, nk = key(nx, ny);
					var t = state.dots.get(nk);
					if (t === undefined) { if (!state.claimed.has(nk)) { free++; cells.push(nx, ny); } }
				}
			}
			if (free <= maxFree) for (var i = 0; i < cells.length; i += 2) cand.add(key(cells[i], cells[i + 1]));
		});
		var out = [];
		cand.forEach(function (nk) {
			var p = parseKey(nk);
			var x = p[0], y = p[1];
			var own = 0;
			for (var dx = -1; dx <= 1 && own < 2; dx++) {
				for (var dy = -1; dy <= 1; dy++) {
					if (dx === 0 && dy === 0) continue;
					if (state.dots.get(key(x + dx, y + dy)) === side) { own++; if (own >= 2) break; }
				}
			}
			if (own < 2) return;
			var log = applyMove(state, x, y);
			if (log.ok) {
				if (log.capturedCount > 0) out.push({ x: x, y: y, cap: log.capturedCount, s: 0 });
				undoMove(state, log);
			}
		});
		out.sort(function (a, b) { return b.cap - a.cap; });
		if (out.length > limit) out.length = limit;
		return out;
	}

	/*
	 * Candidate moves: near every dot on the board, plus (when `detect`) every
	 * capture, so the search never prunes a finishing move.
	 */
	function generateMoves(state, ctx, ply, cap, detect) {
		var side = state.turn;
		var cand = new Set();
		var i;

		function add(x, y) {
			var nk = key(x, y);
			if (cand.has(nk)) return;
			if (!canPlace(state, x, y)) return;
			cand.add(nk);
		}

		state.dots.forEach(function (v, k) {
			if (v !== P1 && v !== P2) return;
			var p = parseKey(k);
			var x = p[0], y = p[1];
			for (i = 0; i < RING1.length; i++) add(x + RING1[i][0], y + RING1[i][1]);
			if (v !== side) {
				for (i = 0; i < RING2FULL.length; i++) add(x + RING2FULL[i][0], y + RING2FULL[i][1]);
			}
		});

		var arr = [];
		cand.forEach(function (nk) {
			var p = parseKey(nk);
			arr.push({ x: p[0], y: p[1], s: orderScore(state, p[0], p[1], side, ctx, ply), cap: 0 });
		});
		arr.sort(function (a, b) { return b.s - a.s; });
		var limit = cap === undefined ? ctx.maxMoves : cap;

		if (detect && ctx.captureScan > 0) {
			var caps = captureMoves(state, ctx.captureFree, ctx.captureScan);
			if (caps.length) {
				var seen = Object.create(null);
				for (i = 0; i < caps.length; i++) seen[key(caps[i].x, caps[i].y)] = 1;
				var rest = [];
				for (i = 0; i < arr.length; i++) {
					if (!seen[key(arr[i].x, arr[i].y)]) rest.push(arr[i]);
				}
				var out = caps.concat(rest);
				if (out.length > limit) out.length = limit;
				return out;
			}
		}

		if (arr.length > limit) arr.length = limit;
		return arr;
	}

	/*
	 * Root move list: wide generation, every candidate played once so that
	 * captures are found even when the finishing move is far from the enemy.
	 */
	function rootMoves(state, ctx) {
		var cands = generateMoves(state, ctx, 0, ctx.testCap, true);
		var caps = [];
		var rest = [];
		for (var i = 0; i < cands.length; i++) {
			var mv = cands[i];
			if (mv.cap > 0) { caps.push(mv); continue; }
			var log = applyMove(state, mv.x, mv.y);
			if (!log.ok) continue;
			if (log.capturedCount > 0) { mv.cap = log.capturedCount; caps.push(mv); }
			else rest.push(mv);
			undoMove(state, log);
			if (now() > ctx.deadline) break;
		}
		caps.sort(function (a, b) { return b.cap - a.cap; });
		rest.sort(function (a, b) { return b.s - a.s; });
		var out = caps.concat(rest);
		if (out.length > ctx.rootLimit) out.length = ctx.rootLimit;
		return out;
	}

	/*
	 * Quiescence: at the horizon, keep taking captures instead of trusting a
	 * static score in the middle of a fight. Stand-pat is the evaluation; only
	 * real captures are searched, so this is cheap and never explodes.
	 */
	function* quiesce(state, alpha, beta, ctx, ply, qd) {
		var stand = evaluate(state, ctx.ai);
		if (qd <= 0) return stand;
		var maximizing = (state.turn === ctx.ai);
		if (maximizing) { if (stand >= beta) return stand; if (stand > alpha) alpha = stand; }
		else { if (stand <= alpha) return stand; if (stand < beta) beta = stand; }

		var caps = captureMoves(state, ctx.captureFree, ctx.qLimit);
		if (!caps.length) return stand;
		var best = stand;
		for (var i = 0; i < caps.length; i++) {
			var mv = caps[i];
			var log = applyMove(state, mv.x, mv.y);
			if (!log.ok) continue;
			var v;
			try { v = yield* quiesce(state, alpha, beta, ctx, ply + 1, qd - 1); }
			finally { undoMove(state, log); }
			if (maximizing) { if (v > best) best = v; if (best > alpha) alpha = best; if (alpha >= beta) break; }
			else { if (v < best) best = v; if (best < beta) beta = best; if (alpha >= beta) break; }
		}
		return best;
	}

	/*
	 * Alpha-beta search written as a generator so it can be paused and keep the
	 * page responsive. Transposition table + PVS + late-move reductions. A
	 * position repeated on the current path is a draw (the game has no terminal
	 * state, so this is what makes the engine avoid pointless loops).
	 */
	function* searchGen(state, depth, alpha, beta, ctx, ply, ext) {
		ctx.nodes++;
		if ((ctx.nodes & 255) === 0) {
			if (now() > ctx.deadline) throw TIMEOUT;
			yield;
		}
		if (depth <= 0) return yield* quiesce(state, alpha, beta, ctx, ply, ctx.qMax);

		var pk = positionKey(state);
		var repAdded = false;
		if (ctx.repSet) {
			if (ctx.repSet.has(pk)) return 0;
			ctx.repSet.add(pk);
			repAdded = true;
		}

		try {
			var ttKey = null, ttEntry = null;
			if (ctx.tt) {
				ttKey = pk;
				ttEntry = ctx.tt.get(ttKey) || null;
				if (ttEntry && ttEntry.depth >= depth) {
					if (ttEntry.flag === TT_EXACT) return ttEntry.score;
					if (ttEntry.flag === TT_LOWER && ttEntry.score >= beta) return ttEntry.score;
					if (ttEntry.flag === TT_UPPER && ttEntry.score <= alpha) return ttEntry.score;
				}
			}

			var moves = generateMoves(state, ctx, ply, undefined, ply > 0 && ply <= ctx.tacticalScan);
			if (!moves.length) return evaluate(state, ctx.ai);

			if (ttEntry && ttEntry.x !== null && ttEntry.x !== undefined) {
				for (var t = 1; t < moves.length; t++) {
					if (moves[t].x === ttEntry.x && moves[t].y === ttEntry.y) {
						var first = moves[t];
						moves[t] = moves[0];
						moves[0] = first;
						break;
					}
				}
			}

			var maximizing = (state.turn === ctx.ai);
			var origAlpha = alpha, origBeta = beta;
			var best = maximizing ? -Infinity : Infinity;
			var localBest = null;
			var searched = 0;

			for (var i = 0; i < moves.length; i++) {
				var mv = moves[i];
				var log = applyMove(state, mv.x, mv.y);
				if (!log.ok) continue;

				var capture = log.capturedCount > 0;
				var childDepth = (capture && ext > 0) ? depth : depth - 1;
				var childExt = (capture && ext > 0) ? ext - 1 : ext;

				var reduce = (ctx.lmr !== false && !capture && depth >= 3 && searched >= 3)
					? (searched >= 8 && depth >= 6 ? 2 : 1) : 0;
				var searchDepth = Math.max(1, childDepth - reduce);

				var v;
				try {
					if (reduce > 0) {
						if (maximizing) {
							v = yield* searchGen(state, searchDepth, alpha, alpha + 1, ctx, ply + 1, childExt);
							if (v > alpha) v = yield* searchGen(state, childDepth, alpha, beta, ctx, ply + 1, childExt);
						} else {
							v = yield* searchGen(state, searchDepth, beta - 1, beta, ctx, ply + 1, childExt);
							if (v < beta) v = yield* searchGen(state, childDepth, alpha, beta, ctx, ply + 1, childExt);
						}
					} else if (searched === 0 || !ctx.pvs) {
						v = yield* searchGen(state, childDepth, alpha, beta, ctx, ply + 1, childExt);
					} else if (maximizing) {
						v = yield* searchGen(state, childDepth, alpha, alpha + 1, ctx, ply + 1, childExt);
						if (v > alpha && v < beta) {
							v = yield* searchGen(state, childDepth, alpha, beta, ctx, ply + 1, childExt);
						}
					} else {
						v = yield* searchGen(state, childDepth, beta - 1, beta, ctx, ply + 1, childExt);
						if (v < beta && v > alpha) {
							v = yield* searchGen(state, childDepth, alpha, beta, ctx, ply + 1, childExt);
						}
					}
				} finally {
					undoMove(state, log);
				}
				searched++;

				if (maximizing) {
					if (v > best) { best = v; localBest = mv; }
					if (best > alpha) alpha = best;
				} else {
					if (v < best) { best = v; localBest = mv; }
					if (best < beta) beta = best;
				}
				if (alpha >= beta) {
					if (localBest) {
						var kk = key(localBest.x, localBest.y);
						ctx.history[kk] = (ctx.history[kk] || 0) + depth * depth;
						var kl = ctx.killer[ply] || (ctx.killer[ply] = [null, null]);
						if (kl[0] !== kk) { kl[1] = kl[0]; kl[0] = kk; }
					}
					break;
				}
			}

			if (ttKey && ctx.tt) {
				var flag = best <= origAlpha ? TT_UPPER : (best >= origBeta ? TT_LOWER : TT_EXACT);
				ctx.tt.set(ttKey, {
					depth: depth, flag: flag, score: best,
					x: localBest ? localBest.x : null, y: localBest ? localBest.y : null
				});
				if (ctx.tt.size > ctx.ttMax) ctx.tt.clear();
			}
			return best;
		} finally {
			if (repAdded) ctx.repSet.delete(pk);
		}
	}

	function makeCtx(player, options) {
		options = options || {};
		return {
			nodes: 0,
			deadline: now() + (options.timeBudget || 800),
			maxMoves: options.maxMoves || 14,
			testCap: options.testCap || 400,
			rootLimit: options.rootLimit || 40,
			tacticalScan: options.tacticalScan || 0,
			captureScan: options.captureScan || 0,
			captureFree: options.captureFree === undefined ? 6 : options.captureFree,
			qMax: options.qMax === undefined ? 5 : options.qMax,
			qLimit: options.qLimit || 20,
			tt: options.tt === false ? null : (options.tt instanceof Map ? options.tt : new Map()),
			ttMax: options.ttMax || 200000,
			pvs: options.pvs !== false,
			lmr: options.lmr !== false,
			repSet: new Set(options.seen || []),
			ai: player,
			history: Object.create(null),
			killer: []
		};
	}

	/*
	 * Iterative-deepening alpha-beta. Returns { x, y } or null. `timeBudget` is
	 * a soft cap in milliseconds; `maxDepth` and `maxMoves` bound the search so
	 * the main thread is never blocked for long.
	 */
	function* bestMoveGen(state, player, options) {
		var maxDepth = (options && options.maxDepth) || 6;
		var ctx = makeCtx(player, options);

		var moves = rootMoves(state, ctx);
		if (!moves.length) {
			if (state.dots.size) return null;
			if (state.bounds) {
				return {
					x: Math.floor((state.bounds.x0 + state.bounds.x1) / 2),
					y: Math.floor((state.bounds.y0 + state.bounds.y1) / 2)
				};
			}
			return { x: 0, y: 0 };
		}

		var best = { x: moves[0].x, y: moves[0].y };
		var bestScore = -Infinity;
		var timedOut = false;
		var stable = 0;
		var stableNeed = (options && options.stable) || 0;

		for (var depth = 2; depth <= maxDepth && !timedOut; depth++) {
			if (ctx.tt) {
				var rootE = ctx.tt.get(positionKey(state));
				if (rootE && rootE.x !== null && rootE.x !== undefined) {
					for (var r = 1; r < moves.length; r++) {
						if (moves[r].x === rootE.x && moves[r].y === rootE.y) {
							var tmp = moves[r]; moves[r] = moves[0]; moves[0] = tmp;
							break;
						}
					}
				}
			}
			var alpha = -Infinity;
			var localBest = null;
			var localScore = -Infinity;
			var rsearched = 0;

			for (var i = 0; i < moves.length; i++) {
				var mv = moves[i];
				var log = applyMove(state, mv.x, mv.y);
				if (!log.ok) continue;

				var capture = log.capturedCount > 0;
				var childDepth = capture ? depth : depth - 1;
				var v;
				try {
					if (rsearched === 0 || !ctx.pvs) {
						v = yield* searchGen(state, childDepth, alpha, Infinity, ctx, 1, capture ? 2 : 3);
					} else {
						v = yield* searchGen(state, childDepth, alpha, alpha + 1, ctx, 1, capture ? 2 : 3);
						if (v > alpha) {
							v = yield* searchGen(state, childDepth, alpha, Infinity, ctx, 1, capture ? 2 : 3);
						}
					}
				} catch (e) {
					if (e === TIMEOUT) { timedOut = true; break; }
					throw e;
				} finally {
					undoMove(state, log);
				}
				rsearched++;

				if (v > localScore) { localScore = v; localBest = mv; }
				if (localScore > alpha) alpha = localScore;
				if (now() > ctx.deadline) { timedOut = true; break; }
			}

			if (localBest) {
				if (localBest.x === best.x && localBest.y === best.y) stable++; else stable = 0;
				best = { x: localBest.x, y: localBest.y };
				bestScore = localScore;
				if (ctx.tt) {
					ctx.tt.set(positionKey(state), {
						depth: depth, flag: TT_EXACT, score: localScore,
						x: localBest.x, y: localBest.y
					});
				}
				moves.sort(function (a, b) {
					if (a === localBest) return -1;
					if (b === localBest) return 1;
					return b.s - a.s;
				});
			}
			if (timedOut) break;
			if (stableNeed && stable >= stableNeed && depth >= 4) break;
		}

		return best;
	}

	/*
	 * Synchronous search (no generators). This is the path used by the worker
	 * and by any caller that does not need to yield to the UI, and it is
	 * markedly faster than driving a generator node by node. The generator
	 * versions above remain for the no-worker cooperative fallback.
	 */
	function quiesceSync(state, alpha, beta, ctx, ply, qd) {
		var stand = evaluate(state, ctx.ai);
		if (qd <= 0) return stand;
		var maximizing = (state.turn === ctx.ai);
		if (maximizing) { if (stand >= beta) return stand; if (stand > alpha) alpha = stand; }
		else { if (stand <= alpha) return stand; if (stand < beta) beta = stand; }
		var caps = captureMoves(state, ctx.captureFree, ctx.qLimit);
		if (!caps.length) return stand;
		var best = stand;
		for (var i = 0; i < caps.length; i++) {
			var mv = caps[i];
			var log = applyMove(state, mv.x, mv.y);
			if (!log.ok) continue;
			var v;
			try { v = quiesceSync(state, alpha, beta, ctx, ply + 1, qd - 1); }
			finally { undoMove(state, log); }
			if (maximizing) { if (v > best) best = v; if (best > alpha) alpha = best; if (alpha >= beta) break; }
			else { if (v < best) best = v; if (best < beta) beta = best; if (alpha >= beta) break; }
		}
		return best;
	}

	function searchSync(state, depth, alpha, beta, ctx, ply, ext) {
		ctx.nodes++;
		if ((ctx.nodes & 255) === 0 && now() > ctx.deadline) throw TIMEOUT;
		if (depth <= 0) return quiesceSync(state, alpha, beta, ctx, ply, ctx.qMax);

		var pk = positionKey(state);
		var repAdded = false;
		if (ctx.repSet) {
			if (ctx.repSet.has(pk)) return 0;
			ctx.repSet.add(pk);
			repAdded = true;
		}

		try {
			var ttKey = null, ttEntry = null;
			if (ctx.tt) {
				ttKey = pk;
				ttEntry = ctx.tt.get(ttKey) || null;
				if (ttEntry && ttEntry.depth >= depth) {
					if (ttEntry.flag === TT_EXACT) return ttEntry.score;
					if (ttEntry.flag === TT_LOWER && ttEntry.score >= beta) return ttEntry.score;
					if (ttEntry.flag === TT_UPPER && ttEntry.score <= alpha) return ttEntry.score;
				}
			}

			var moves = generateMoves(state, ctx, ply, undefined, ply > 0 && ply <= ctx.tacticalScan);
			if (!moves.length) return evaluate(state, ctx.ai);

			if (ttEntry && ttEntry.x !== null && ttEntry.x !== undefined) {
				for (var t = 1; t < moves.length; t++) {
					if (moves[t].x === ttEntry.x && moves[t].y === ttEntry.y) {
						var first = moves[t];
						moves[t] = moves[0];
						moves[0] = first;
						break;
					}
				}
			}

			var maximizing = (state.turn === ctx.ai);
			var origAlpha = alpha, origBeta = beta;
			var best = maximizing ? -Infinity : Infinity;
			var localBest = null;
			var searched = 0;

			for (var i = 0; i < moves.length; i++) {
				var mv = moves[i];
				var log = applyMove(state, mv.x, mv.y);
				if (!log.ok) continue;

				var capture = log.capturedCount > 0;
				var childDepth = (capture && ext > 0) ? depth : depth - 1;
				var childExt = (capture && ext > 0) ? ext - 1 : ext;
				var reduce = (ctx.lmr !== false && !capture && depth >= 3 && searched >= 3)
					? (searched >= 8 && depth >= 6 ? 2 : 1) : 0;
				var searchDepth = Math.max(1, childDepth - reduce);

				var v;
				try {
					if (reduce > 0) {
						if (maximizing) {
							v = searchSync(state, searchDepth, alpha, alpha + 1, ctx, ply + 1, childExt);
							if (v > alpha) v = searchSync(state, childDepth, alpha, beta, ctx, ply + 1, childExt);
						} else {
							v = searchSync(state, searchDepth, beta - 1, beta, ctx, ply + 1, childExt);
							if (v < beta) v = searchSync(state, childDepth, alpha, beta, ctx, ply + 1, childExt);
						}
					} else if (searched === 0 || !ctx.pvs) {
						v = searchSync(state, childDepth, alpha, beta, ctx, ply + 1, childExt);
					} else if (maximizing) {
						v = searchSync(state, childDepth, alpha, alpha + 1, ctx, ply + 1, childExt);
						if (v > alpha && v < beta) {
							v = searchSync(state, childDepth, alpha, beta, ctx, ply + 1, childExt);
						}
					} else {
						v = searchSync(state, childDepth, beta - 1, beta, ctx, ply + 1, childExt);
						if (v < beta && v > alpha) {
							v = searchSync(state, childDepth, alpha, beta, ctx, ply + 1, childExt);
						}
					}
				} finally {
					undoMove(state, log);
				}
				searched++;

				if (maximizing) {
					if (v > best) { best = v; localBest = mv; }
					if (best > alpha) alpha = best;
				} else {
					if (v < best) { best = v; localBest = mv; }
					if (best < beta) beta = best;
				}
				if (alpha >= beta) {
					if (localBest) {
						var kk = key(localBest.x, localBest.y);
						ctx.history[kk] = (ctx.history[kk] || 0) + depth * depth;
						var kl = ctx.killer[ply] || (ctx.killer[ply] = [null, null]);
						if (kl[0] !== kk) { kl[1] = kl[0]; kl[0] = kk; }
					}
					break;
				}
			}

			if (ttKey && ctx.tt) {
				var flag = best <= origAlpha ? TT_UPPER : (best >= origBeta ? TT_LOWER : TT_EXACT);
				ctx.tt.set(ttKey, {
					depth: depth, flag: flag, score: best,
					x: localBest ? localBest.x : null, y: localBest ? localBest.y : null
				});
				if (ctx.tt.size > ctx.ttMax) ctx.tt.clear();
			}
			return best;
		} finally {
			if (repAdded) ctx.repSet.delete(pk);
		}
	}

	/*
	 * Iterative-deepening alpha-beta (synchronous). Returns { x, y } or null.
	 * `timeBudget` is a soft cap in milliseconds; `maxDepth`/`maxMoves` bound the
	 * search. `stable` (if set) stops early once the best move has not changed
	 * for that many iterations, which trims the wait on obvious moves.
	 */
	function bestMove(state, player, options) {
		var maxDepth = (options && options.maxDepth) || 6;
		var ctx = makeCtx(player, options);

		var moves = rootMoves(state, ctx);
		if (!moves.length) {
			if (state.dots.size) return null;
			if (state.bounds) {
				return {
					x: Math.floor((state.bounds.x0 + state.bounds.x1) / 2),
					y: Math.floor((state.bounds.y0 + state.bounds.y1) / 2)
				};
			}
			return { x: 0, y: 0 };
		}

		var best = { x: moves[0].x, y: moves[0].y };
		var bestScore = -Infinity;
		var timedOut = false;
		var stable = 0;
		var stableNeed = (options && options.stable) || 0;

		for (var depth = 2; depth <= maxDepth && !timedOut; depth++) {
			if (ctx.tt) {
				var rootE = ctx.tt.get(positionKey(state));
				if (rootE && rootE.x !== null && rootE.x !== undefined) {
					for (var r = 1; r < moves.length; r++) {
						if (moves[r].x === rootE.x && moves[r].y === rootE.y) {
							var tmp = moves[r]; moves[r] = moves[0]; moves[0] = tmp;
							break;
						}
					}
				}
			}
			var alpha = -Infinity;
			var localBest = null;
			var localScore = -Infinity;
			var rsearched = 0;

			for (var i = 0; i < moves.length; i++) {
				var mv = moves[i];
				var log = applyMove(state, mv.x, mv.y);
				if (!log.ok) continue;

				var capture = log.capturedCount > 0;
				var childDepth = capture ? depth : depth - 1;
				var v;
				try {
					if (rsearched === 0 || !ctx.pvs) {
						v = searchSync(state, childDepth, alpha, Infinity, ctx, 1, capture ? 2 : 3);
					} else {
						v = searchSync(state, childDepth, alpha, alpha + 1, ctx, 1, capture ? 2 : 3);
						if (v > alpha) {
							v = searchSync(state, childDepth, alpha, Infinity, ctx, 1, capture ? 2 : 3);
						}
					}
				} catch (e) {
					if (e === TIMEOUT) { timedOut = true; break; }
					throw e;
				} finally {
					undoMove(state, log);
				}
				rsearched++;

				if (v > localScore) { localScore = v; localBest = mv; }
				if (localScore > alpha) alpha = localScore;
				if (now() > ctx.deadline) { timedOut = true; break; }
			}

			if (localBest) {
				if (localBest.x === best.x && localBest.y === best.y) stable++; else stable = 0;
				best = { x: localBest.x, y: localBest.y };
				bestScore = localScore;
				if (ctx.tt) {
					ctx.tt.set(positionKey(state), {
						depth: depth, flag: TT_EXACT, score: localScore,
						x: localBest.x, y: localBest.y
					});
				}
				moves.sort(function (a, b) {
					if (a === localBest) return -1;
					if (b === localBest) return 1;
					return b.s - a.s;
				});
			}
			if (timedOut) break;
			if (stableNeed && stable >= stableNeed && depth >= 4) break;
		}

		return best;
	}

	/*
	 * Like bestMove, but returns the top `count` root moves ranked by score
	 * (highest first). The root is searched with a full window so the scores of
	 * the alternatives are comparable, not just cut off. Used to pick a random
	 * move among the best few.
	 */
	function* bestMovesGen(state, player, options, count) {
		count = Math.max(1, count || 1);
		var maxDepth = (options && options.maxDepth) || 6;
		var ctx = makeCtx(player, options);

		var moves = rootMoves(state, ctx);
		if (!moves.length) {
			if (state.dots.size) return [];
			if (state.bounds) {
				return [{
					x: Math.floor((state.bounds.x0 + state.bounds.x1) / 2),
					y: Math.floor((state.bounds.y0 + state.bounds.y1) / 2)
				}];
			}
			return [{ x: 0, y: 0 }];
		}

		var ranked = [];
		var stop = false;
		for (var depth = 2; depth <= maxDepth && !stop; depth++) {
			var scores = new Array(moves.length);
			for (var i = 0; i < moves.length; i++) {
				var mv = moves[i];
				var log = applyMove(state, mv.x, mv.y);
				if (!log.ok) { scores[i] = -Infinity; continue; }
				var capture = log.capturedCount > 0;
				var childDepth = capture ? depth : depth - 1;
				var v;
				try {
					v = yield* searchGen(state, childDepth, -Infinity, Infinity, ctx, 1, capture ? 2 : 3);
				} catch (e) {
					if (e === TIMEOUT) { stop = true; }
					else throw e;
				} finally {
					undoMove(state, log);
				}
				if (stop) break;
				scores[i] = v;
				if (now() > ctx.deadline) { stop = true; break; }
			}
			if (stop) break;
			ranked = moves.map(function (m, idx) { return { x: m.x, y: m.y, score: scores[idx] }; });
			ranked.sort(function (a, b) { return b.score - a.score; });
			var order = Object.create(null);
			ranked.forEach(function (r, idx) { order[key(r.x, r.y)] = idx; });
			moves.sort(function (a, b) {
				return (order[key(a.x, a.y)] || 0) - (order[key(b.x, b.y)] || 0);
			});
		}

		if (!ranked.length) {
			ranked = moves.slice(0, count).map(function (m) { return { x: m.x, y: m.y, score: m.s }; });
		}
		return ranked.slice(0, count);
	}

	/* Synchronous wrapper: drives the generator to completion. */
	function bestMoves(state, player, options, count) {
		var it = bestMovesGen(state, player, options, count);
		var step = it.next();
		while (!step.done) step = it.next();
		return step.value;
	}

	var api = {
		EMPTY: EMPTY, P1: P1, P2: P2, C1: C1, C2: C2,
		key: key,
		parseKey: parseKey,
		other: other,
		isActive: isActive,
		isPrisoner: isPrisoner,
		ownerOf: ownerOf,
		createGame: createGame,
		clone: clone,
		inBounds: inBounds,
		canPlace: canPlace,
		place: place,
		applyMove: applyMove,
		undoMove: undoMove,
		componentsFor: componentsFor,
		activeCount: activeCount,
		prisonerCount: prisonerCount,
		isGameOver: isGameOver,
		seed: seed,
		isGrounded: isGrounded,
		hasAnyMove: hasAnyMove,
		evaluate: evaluate,
		setWeights: setWeights,
		hash: positionKey,
		bestMove: bestMove,
		bestMoves: bestMoves,
		bestMoveGen: bestMoveGen,
		bestMovesGen: bestMovesGen
	};

	root.DotsEngine = api;
	if (typeof module !== 'undefined' && module.exports) module.exports = api;
})(typeof window !== 'undefined' ? window : globalThis);
