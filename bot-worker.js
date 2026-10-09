/*
 * Bot search worker (same-origin file variant).
 *
 * The strongest level thinks for several seconds; running that on the main
 * thread would freeze the page. The engine is pure logic, so it can be loaded
 * here directly and run off the UI thread. The board state travels as plain
 * arrays (Map entries) and is rebuilt before the search.
 *
 * The worker also keeps a transposition table between requests and can "ponder"
 * while it is the opponent's turn: it searches the human's position in short
 * slices, so the worker stays responsive and the search can be cancelled the
 * moment a real move arrives. Both make the next real search deeper.
 */
importScripts('engine.js');

var TT = new Map();
var TT_MAX = 400000;
var ponder = null; /* { cancel: boolean } while a background search is running */

function buildState(d) {
	return {
		dots: new Map(d.dots),
		claimed: new Map(d.claimed),
		turn: d.turn,
		score: d.score,
		rules: d.rules,
		bounds: d.bounds || null,
		lastMove: d.lastMove || null,
		moveCount: d.moveCount
	};
}

function searchOptions(d, budget) {
	var o = {};
	if (d.options) for (var k in d.options) o[k] = d.options[k];
	o.tt = TT;
	o.ttMax = TT_MAX;
	o.timeBudget = budget;
	return o;
}

function cancelPonder() {
	if (ponder) { ponder.cancel = true; ponder = null; }
}

function startPonder(d) {
	cancelPonder();
	var state = buildState(d);
	/* A large budget: the search runs until the next real request cancels it. */
	var gen = self.DotsEngine.bestMoveGen(state, d.player, searchOptions(d, 600000));
	var p = { cancel: false };
	ponder = p;
	function slice() {
		if (p.cancel || ponder !== p) return;
		var end = Date.now() + 24;
		var r;
		do { r = gen.next(); } while (!r.done && Date.now() < end);
		if (r.done) { if (ponder === p) ponder = null; return; }
		setTimeout(slice, 0);
	}
	setTimeout(slice, 0);
}

self.onmessage = function (ev) {
	var d = ev.data || {};

	if (d.type === 'reset') { cancelPonder(); TT.clear(); return; }
	if (d.type === 'stop') { cancelPonder(); return; }
	if (d.type === 'ponder') { startPonder(d); return; }

	/* A real move request: stop pondering and search synchronously. */
	cancelPonder();
	var state = buildState(d);
	var options = searchOptions(d, d.options && d.options.timeBudget);
	var moves = [];
	try {
		if ((d.count || 1) <= 1) {
			var best = self.DotsEngine.bestMove(state, d.player, options);
			moves = best ? [best] : [];
		} else {
			moves = self.DotsEngine.bestMoves(state, d.player, options, d.count) || [];
		}
	} catch (err) {
		moves = [];
	}
	self.postMessage({ id: d.id, moves: moves });
};
