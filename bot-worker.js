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
	var move = null;
	try {
		move = self.DotsEngine.bestMove(state, d.player, d.options);
	} catch (err) {
		move = null;
	}
	self.postMessage({ id: d.id, move: move });
};
