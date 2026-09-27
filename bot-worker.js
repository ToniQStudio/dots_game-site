/*
 * Bot search worker (same-origin file variant).
 *
 * The strongest level thinks for several seconds; running that on the main
 * thread would freeze the page. The engine is pure logic, so it can be loaded
 * here directly and run off the UI thread. The board state travels as plain
 * arrays (Map entries) and is rebuilt before the search.
 */
importScripts('engine.js');

self.onmessage = function (ev) {
	var d = ev.data || {};
	var state = {
		dots: new Map(d.dots),
		claimed: new Map(d.claimed),
		turn: d.turn,
		score: d.score,
		rules: d.rules,
		bounds: d.bounds || null,
		lastMove: d.lastMove || null,
		moveCount: d.moveCount
	};
	var moves = [];
	try {
		if ((d.count || 1) <= 1) {
			var best = self.DotsEngine.bestMove(state, d.player, d.options);
			moves = best ? [best] : [];
		} else {
			moves = self.DotsEngine.bestMoves(state, d.player, d.options, d.count) || [];
		}
	} catch (err) {
		moves = [];
	}
	self.postMessage({ id: d.id, moves: moves });
};
