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
 *   - capture extensions, so forced capture chains are followed past the
 *     horizon;
 *   - move ordering (capture proximity, killers, history) and a node/time
 *     budget, so it deepens until the browser would otherwise stall;
 *   - a heuristic that scores material, connectivity, "freedom" (liberties)
 *     and encirclement pressure, so it both builds fortresses and defends.
 * The game has no terminal state (the board never fills, the loser can always
 * play on), so "play to the end" is impossible by definition; iterative
 * deepening plus the budget is the practical maximum.
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

	function key(x, y) { return x + ',' + y; }

	function parseKey(k) {
		var i = k.indexOf(',');
		return [+k.slice(0, i), +k.slice(i + 1)];
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

		state.dots.set(k0, player);
		log.dotChanges.push({ k: k0, old: undefined });
		state.moveCount++;
		state.lastMove = { x: x, y: y, player: player };

		var comps = componentsFor(state, player);
		var i, j;
		for (i = 0; i < comps.length; i++) {
			var comp = comps[i];
			var enemies = [];
			for (j = 0; j < comp.length; j++) {
				if (state.dots.get(key(comp[j][0], comp[j][1])) === foe) enemies.push(comp[j]);
			}
			if (!enemies.length) continue;
			for (j = 0; j < enemies.length; j++) {
				var ek = key(enemies[j][0], enemies[j][1]);
				log.dotChanges.push({ k: ek, old: state.dots.get(ek) });
				state.dots.set(ek, prisonerValue(foe));
				log.captured.push({ x: enemies[j][0], y: enemies[j][1] });
			}
			for (j = 0; j < comp.length; j++) {
				var ck = key(comp[j][0], comp[j][1]);
				log.claimedChanges.push({ k: ck, old: state.claimed.get(ck) });
				state.claimed.set(ck, player);
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
			if (c.old === undefined) state.dots.delete(c.k);
			else state.dots.set(c.k, c.old);
		}
		for (i = log.claimedChanges.length - 1; i >= 0; i--) {
			c = log.claimedChanges[i];
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

	/* ==================================================================== AI */

	/*
	 * Static score of a position, from `ai`'s point of view.
	 *   material   — captured prisoners (the win condition), dominant;
	 *   structure  — connected dots are stronger than loose ones;
	 *   freedom    — empty neighbours act as liberties; a dot with almost no
	 *                freedom is one move away from being surrounded;
	 *   pressure   — dots of mine crowding the enemy, minus enemy dots
	 *                crowding mine.
	 */
	function evaluate(state, ai) {
		var opp = other(ai);
		var val = (state.score[ai] - state.score[opp]) * 100;

		var ownConn = 0, oppConn = 0;
		var ownFree = 0, oppFree = 0;
		var ownTrap = 0, oppTrap = 0;
		var pressure = 0, attacked = 0;

		state.dots.forEach(function (v, k) {
			if (v !== P1 && v !== P2) return;
			var p = parseKey(k);
			var x = p[0], y = p[1];
			var own = 0, foe = 0, free = 0;
			for (var dx = -1; dx <= 1; dx++) {
				for (var dy = -1; dy <= 1; dy++) {
					if (dx === 0 && dy === 0) continue;
					var nk = key(x + dx, y + dy);
					var t = state.dots.get(nk);
					if (t === v) own++;
					else if (t === P1 || t === P2) foe++;
					else if (!state.claimed.has(nk)) free++;
				}
			}
			if (v === ai) {
				ownConn += own; ownFree += free; pressure += foe;
				if (free <= 1) ownTrap++;
			} else {
				oppConn += own; oppFree += free; attacked += foe;
				if (free <= 1) oppTrap++;
			}
		});

		val += (ownConn - oppConn) * 1.5;
		val += (ownFree - oppFree) * 0.3;
		val += (oppTrap - ownTrap) * 6;
		val += (attacked - pressure) * 0.8;
		return val;
	}

	/*
	 * Order a candidate: crowding the enemy is attacking, staying near your own
	 * dots builds walls. Killers and history from earlier cutoffs come first.
	 */
	function orderScore(state, x, y, side, ctx, ply) {
		var score = 0;
		var foe = other(side);
		for (var dx = -2; dx <= 2; dx++) {
			for (var dy = -2; dy <= 2; dy++) {
				if (dx === 0 && dy === 0) continue;
				var v = state.dots.get(key(x + dx, y + dy));
				if (v === undefined) continue;
				var d = Math.max(Math.abs(dx), Math.abs(dy));
				if (v === foe) score += (3 - d) * 3;
				else if (v === side) score += (3 - d);
			}
		}
		var kk = key(x, y);
		var killers = ctx.killer[ply];
		if (killers) {
			if (killers[0] === kk) score += 40;
			else if (killers[1] === kk) score += 30;
		}
		score += (ctx.history[kk] || 0) * 0.01;
		return score;
	}

	function generateMoves(state, ctx, ply, cap, detect) {
		var side = state.turn;
		var cand = new Set();
		state.dots.forEach(function (v, k) {
			if (v !== P1 && v !== P2) return;
			var p = parseKey(k);
			var x = p[0], y = p[1];
			var r = (v === side) ? 1 : 2;
			for (var dx = -r; dx <= r; dx++) {
				for (var dy = -r; dy <= r; dy++) {
					if (dx === 0 && dy === 0) continue;
					var nx = x + dx, ny = y + dy;
					var nk = key(nx, ny);
					if (cand.has(nk)) continue;
					if (!canPlace(state, nx, ny)) continue;
					cand.add(nk);
				}
			}
		});
		var arr = [];
		cand.forEach(function (nk) {
			var p = parseKey(nk);
			arr.push({ x: p[0], y: p[1], s: orderScore(state, p[0], p[1], side, ctx, ply), cap: 0 });
		});
		arr.sort(function (a, b) { return b.s - a.s; });
		var limit = cap === undefined ? ctx.maxMoves : cap;

		/*
		 * Capture-aware generation. Playing a move and looking at what it takes
		 * is expensive, so it is done only where it matters most — at the very
		 * first reply — and only for the top `captureScan` candidates. Every
		 * capture found is kept even if it would not fit the move limit, so the
		 * search never overlooks a capture by either side.
		 */
		if (detect && ctx.captureScan > 0 && arr.length) {
			var scan = Math.min(arr.length, ctx.captureScan);
			var caps = [], rest = [];
			for (var i = 0; i < scan; i++) {
				var mv = arr[i];
				var log = applyMove(state, mv.x, mv.y);
				if (!log.ok) continue;
				if (log.capturedCount > 0) { mv.cap = log.capturedCount; caps.push(mv); }
				else rest.push(mv);
				undoMove(state, log);
			}
			for (var j = scan; j < arr.length; j++) rest.push(arr[j]);
			caps.sort(function (a, b) { return b.cap - a.cap; });
			rest.sort(function (a, b) { return b.s - a.s; });
			if (caps.length >= limit) return caps.slice(0, limit);
			return caps.concat(rest.slice(0, limit - caps.length));
		}

		if (arr.length > limit) arr.length = limit;
		return arr;
	}

	/*
	 * Root move list. Every candidate is played and unmade so that capturing
	 * moves are identified and placed first — a finishing move can sit on the
	 * far side of a large loop, far from the enemy, and static ordering alone
	 * could drop it.
	 */
	function rootMoves(state, ctx) {
		var cands = generateMoves(state, ctx, 0, ctx.testCap);
		var caps = [];
		var rest = [];
		for (var i = 0; i < cands.length; i++) {
			var mv = cands[i];
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
	 * Alpha-beta search written as a generator so it can be paused between
	 * slices of work (yield) and keep the page responsive even without a web
	 * worker. `bestMove` drives it to completion in one go.
	 */
	function* searchGen(state, depth, alpha, beta, ctx, ply, ext) {
		ctx.nodes++;
		if ((ctx.nodes & 255) === 0) {
			if (now() > ctx.deadline) throw TIMEOUT;
			yield;
		}
		if (depth <= 0) return evaluate(state, ctx.ai);

		var moves = generateMoves(state, ctx, ply, undefined, ply > 0 && ply <= ctx.tacticalScan);
		if (!moves.length) return evaluate(state, ctx.ai);

		var maximizing = (state.turn === ctx.ai);
		var best = maximizing ? -Infinity : Infinity;
		var localBest = null;

		for (var i = 0; i < moves.length; i++) {
			var mv = moves[i];
			var log = applyMove(state, mv.x, mv.y);
			if (!log.ok) continue;

			var capture = log.capturedCount > 0;
			var childDepth = (capture && ext > 0) ? depth : depth - 1;
			var childExt = (capture && ext > 0) ? ext - 1 : ext;

			var v;
			try {
				v = yield* searchGen(state, childDepth, alpha, beta, ctx, ply + 1, childExt);
			} finally {
				undoMove(state, log);
			}

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
		return best;
	}

	/*
	 * Iterative-deepening alpha-beta. Returns { x, y } or null. `timeBudget` is
	 * a soft cap in milliseconds; `maxDepth` and `maxMoves` bound the search so
	 * the main thread is never blocked for long.
	 */
	function* bestMoveGen(state, player, options) {
		options = options || {};
		var timeBudget = options.timeBudget || 800;
		var maxDepth = options.maxDepth || 6;
		var ctx = {
			nodes: 0,
			deadline: now() + timeBudget,
			maxMoves: options.maxMoves || 14,
			testCap: options.testCap || 400,
			rootLimit: options.rootLimit || 40,
			tacticalScan: options.tacticalScan || 0,
			captureScan: options.captureScan || 0,
			ai: player,
			history: Object.create(null),
			killer: []
		};

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

		for (var depth = 2; depth <= maxDepth && !timedOut; depth++) {
			var alpha = -Infinity;
			var localBest = null;
			var localScore = -Infinity;

			for (var i = 0; i < moves.length; i++) {
				var mv = moves[i];
				var log = applyMove(state, mv.x, mv.y);
				if (!log.ok) continue;

				var capture = log.capturedCount > 0;
				var childDepth = capture ? depth : depth - 1;
				var v;
				try {
					v = yield* searchGen(state, childDepth, alpha, Infinity, ctx, 1, capture ? 2 : 3);
				} catch (e) {
					if (e === TIMEOUT) { timedOut = true; break; }
					throw e;
				} finally {
					undoMove(state, log);
				}

				if (v > localScore) { localScore = v; localBest = mv; }
				if (localScore > alpha) alpha = localScore;
				if (now() > ctx.deadline) { timedOut = true; break; }
			}

			if (localBest) {
				best = { x: localBest.x, y: localBest.y };
				bestScore = localScore;
				/* best-first ordering for the next, deeper iteration */
				moves.sort(function (a, b) {
					if (a === localBest) return -1;
					if (b === localBest) return 1;
					return b.s - a.s;
				});
			}
			if (timedOut) break;
		}

		return best;
	}

	/* Synchronous wrapper: drives the generator to completion. */
	function bestMove(state, player, options) {
		var it = bestMoveGen(state, player, options);
		var step = it.next();
		while (!step.done) step = it.next();
		return step.value;
	}

	/*
	 * Like bestMove, but returns the top `count` root moves ranked by score
	 * (highest first). The root is searched with a full window so the scores of
	 * the alternatives are comparable, not just cut off. Used to pick a random
	 * move among the best few.
	 */
	function* bestMovesGen(state, player, options, count) {
		options = options || {};
		count = Math.max(1, count || 1);
		var timeBudget = options.timeBudget || 800;
		var maxDepth = options.maxDepth || 6;
		var ctx = {
			nodes: 0,
			deadline: now() + timeBudget,
			maxMoves: options.maxMoves || 14,
			testCap: options.testCap || 400,
			rootLimit: options.rootLimit || 40,
			tacticalScan: options.tacticalScan || 0,
			captureScan: options.captureScan || 0,
			ai: player,
			history: Object.create(null),
			killer: []
		};

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
			/* carry the ranking into the next, deeper iteration */
			var order = Object.create(null);
			ranked.forEach(function (r, idx) { order[r.x + ',' + r.y] = idx; });
			moves.sort(function (a, b) {
				return (order[a.x + ',' + a.y] || 0) - (order[b.x + ',' + b.y] || 0);
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
		evaluate: evaluate,
		bestMove: bestMove,
		bestMoves: bestMoves,
		bestMoveGen: bestMoveGen,
		bestMovesGen: bestMovesGen
	};

	root.DotsEngine = api;
	if (typeof module !== 'undefined' && module.exports) module.exports = api;
})(typeof window !== 'undefined' ? window : globalThis);
