/*
 * "Точки" — interface layer.
 * The board is an infinite lattice shown through a camera: drag to pan, wheel
 * or pinch to zoom, buttons to zoom and jump back to the last move. Dots are
 * drawn straight from the game state; fortress outlines only appear once enemy
 * dots are actually enclosed, a segment that has been drawn once is permanent,
 * and new enclosures attach to an existing outline instead of redrawing it.
 */
(function () {
	'use strict';

	var E = window.DotsEngine;
	var TAU = Math.PI * 2;
	var BASE_CELL = 34;
	var ZOOM_LEVELS = [0.5, 0.75, 1, 1.25, 1.5];
	/* Navigation shows multipliers rather than percentages. */
	var ZOOM_LABELS = ['×1', '×2', '×3', '×5', '×6'];
	var MIN_ZOOM = ZOOM_LEVELS[0];
	var MAX_ZOOM = ZOOM_LEVELS[ZOOM_LEVELS.length - 1];

	/* Field size — side length in cells; null is the endless board. */
	var FIELD_SIZES = { small: 20, medium: 40, infinite: null };

	/*
	 * Game-time choices in seconds. There is no upper limit: after five
	 * minutes every step adds another five minutes. "Без учёта" turns the
	 * clock off entirely.
	 */
	function timeAt(index) {
		var base = [20, 40, 60, 120, 180, 300];
		if (index < base.length) return base[Math.max(0, index)];
		return 300 + (index - 5) * 300;
	}

	/*
	 * Bot presets. Every level searches roughly three times deeper and wider
	 * than before and never plays a deliberately random move: the computer
	 * always commits to the move it believes is best, so the whole search is
	 * aimed at winning. `tacticalScan` and `captureScan` make it look at
	 * captures in the first reply, so it never overlooks a capture by either
	 * side.
	 */
	var DIFFICULTY = {
		easy: { timeBudget: 2100, maxDepth: 7, maxMoves: 16, rootLimit: 70, tacticalScan: 1, captureScan: 40 },
		medium: { timeBudget: 4500, maxDepth: 13, maxMoves: 30, rootLimit: 100, tacticalScan: 1, captureScan: 76 },
		hard: { timeBudget: 16000, maxDepth: 22, maxMoves: 56, rootLimit: 190, tacticalScan: 1, captureScan: 120 }
	};

	/*
	 * Anti-repetition safety valve. On an endless board a deadlock can repeat
	 * forever: the human has a single move that avoids capture and the computer
	 * a single move that keeps the threat, so nothing ever changes. If the
	 * computer goes this many of its own moves in a row without anyone being
	 * captured, it stops insisting on the top move and plays its second-best
	 * one, which breaks the loop and lets the game progress.
	 */
	var REPEAT_AFTER = 10;

	var NAMES = { 1: 'Синие', 2: 'Красные' };

	var BADGE_TROPHY =
		'<svg viewBox="0 0 24 24"><path d="M8 21h8M12 17v4M6 3h12v5a6 6 0 0 1-12 0z"/><path d="M6 5H3v2a4 4 0 0 0 4 4M18 5h3v2a4 4 0 0 1-4 4"/></svg>';
	var BADGE_HANDSHAKE =
		'<svg viewBox="0 0 24 24"><path d="M11 17 8.5 14.5a2.1 2.1 0 0 1 3-3l1 1 1-1a2.1 2.1 0 0 1 3 3L13 17"/><path d="M2 12l4-4 5 5M22 12l-4-4-5 5"/></svg>';

	var els = {};
	var ui = {
		ctx: null,
		metrics: null,
		cam: { x: 0, y: 0, zoom: 1 },
		scene: { edges: [] },
		state: null,
		history: [],
		mode: 'pvp',
		started: false,
		size: 'infinite',
		difficulty: 'medium',
		first: 'human',
		timeLimit: 0,
		timeIndex: 0,
		deadline: null,
		clockTimer: null,
		thinkTimer: null,
		thinkStart: 0,
		panelHidden: false,
		botWorker: null,
		botWorkerUrl: null,
		botWorkerKind: null,
		botWorkerKinds: ['file', 'blob'],
		botWorkerFailed: false,
		botPending: null,
		botRequestId: 0,
		botMoves: 0,
		botQuiet: 0,
		botAlt: false,
		cursor: { x: 0, y: 0 },
		keyboard: false,
		hover: null,
		flash: null,
		thinking: false,
		ended: false,
		palette: null,
		pointers: new Map(),
		gesture: null,
		wheelAccum: 0
	};

	/* --------------------------------------------------------------- utils --- */

	function $(id) { return document.getElementById(id); }
	function clamp(v, lo, hi) { return v < lo ? lo : v > hi ? hi : v; }
	function scale() { return BASE_CELL * ui.cam.zoom; }

	function pointsWord(n) {
		var m10 = n % 10, m100 = n % 100;
		if (m10 === 1 && m100 !== 11) return 'точку';
		if (m10 >= 2 && m10 <= 4 && (m100 < 12 || m100 > 14)) return 'точки';
		return 'точек';
	}

	function readPalette() {
		var cs = getComputedStyle(document.documentElement);
		function v(name) { return cs.getPropertyValue(name).trim(); }
		return {
			boardPaper: v('--board-paper'),
			grid: v('--grid'),
			gridBold: v('--grid-bold'),
			p1: v('--p1'), p2: v('--p2'),
			p1Captured: v('--p1-captured'), p2Captured: v('--p2-captured'),
			accent: v('--focus'), danger: v('--danger')
		};
	}

	function updateThemeButton() {
		if (!els.themeBtn) return;
		var dark = document.documentElement.getAttribute('data-theme') === 'dark';
		els.themeBtn.setAttribute('aria-label', dark ? 'Включить светлую тему' : 'Включить тёмную тему');
		els.themeBtn.setAttribute('title', dark ? 'Светлая тема' : 'Тёмная тема');
	}

	function setTheme(theme) {
		document.documentElement.setAttribute('data-theme', theme);
		ui.palette = readPalette();
		updateThemeButton();
		render();
	}

	/* ------------------------------------------------------------ camera --- */

	function fit() {
		var frame = els.boardFrame;
		var cs = getComputedStyle(frame);
		var padX = parseFloat(cs.paddingLeft) + parseFloat(cs.paddingRight);
		var padY = parseFloat(cs.paddingTop) + parseFloat(cs.paddingBottom);
		var cssW = Math.max(200, frame.clientWidth - padX);
		var cssH = Math.max(200, frame.clientHeight - padY);
		var dpr = Math.min(window.devicePixelRatio || 1, 2);
		els.canvas.style.width = cssW + 'px';
		els.canvas.style.height = cssH + 'px';
		els.canvas.width = Math.round(cssW * dpr);
		els.canvas.height = Math.round(cssH * dpr);
		ui.metrics = { cssW: cssW, cssH: cssH, dpr: dpr };
		ui.ctx = els.canvas.getContext('2d');
	}

	function panelInsetX() {
		if (ui.panelHidden) return 0;
		if (window.innerWidth <= 900) return 0;
		return els.panel ? els.panel.offsetWidth : 0;
	}

	/* Screen x the camera is centred on: the middle of the visible strip when
	   the side panel is open, otherwise the middle of the window. */
	function viewCenterX() {
		return (ui.metrics.cssW - panelInsetX()) / 2;
	}

	function worldToScreen(wx, wy) {
		var sc = scale();
		return [viewCenterX() + (wx - ui.cam.x) * sc, ui.metrics.cssH / 2 + (wy - ui.cam.y) * sc];
	}

	function screenToWorld(sx, sy) {
		var sc = scale();
		return [ui.cam.x + (sx - viewCenterX()) / sc, ui.cam.y + (sy - ui.metrics.cssH / 2) / sc];
	}

	function localPoint(evt) {
		var rect = els.canvas.getBoundingClientRect();
		return { x: evt.clientX - rect.left, y: evt.clientY - rect.top };
	}

	function nodeAtScreen(sx, sy) {
		var world = screenToWorld(sx, sy);
		var x = Math.round(world[0]);
		var y = Math.round(world[1]);
		var sc = scale();
		var dx = sx - (viewCenterX() + (x - ui.cam.x) * sc);
		var dy = sy - (ui.metrics.cssH / 2 + (y - ui.cam.y) * sc);
		if (Math.sqrt(dx * dx + dy * dy) > sc * 0.62) return null;
		return { x: x, y: y };
	}

	function zoomIndex() {
		var best = 0, bestDist = Infinity;
		for (var i = 0; i < ZOOM_LEVELS.length; i++) {
			var d = Math.abs(ZOOM_LEVELS[i] - ui.cam.zoom);
			if (d < bestDist) { bestDist = d; best = i; }
		}
		return best;
	}

	/* Zoom is discrete: always one of ZOOM_LEVELS, anchored at a screen point. */
	function setZoomAtScreen(sx, sy, level) {
		var before = screenToWorld(sx, sy);
		ui.cam.zoom = clamp(level, MIN_ZOOM, MAX_ZOOM);
		var after = screenToWorld(sx, sy);
		ui.cam.x += before[0] - after[0];
		ui.cam.y += before[1] - after[1];
	}

	function stepZoom(dir, sx, sy) {
		var i = clamp(zoomIndex() + dir, 0, ZOOM_LEVELS.length - 1);
		setZoomAtScreen(sx, sy, ZOOM_LEVELS[i]);
	}

	function levelForFit(fitZoom) {
		var level = ZOOM_LEVELS[0];
		for (var i = ZOOM_LEVELS.length - 1; i >= 0; i--) {
			if (ZOOM_LEVELS[i] <= fitZoom) { level = ZOOM_LEVELS[i]; break; }
		}
		return level;
	}

	/* Keep a bounded board from being dragged far out of view. */
	function clampCamera() {
		var b = ui.state && ui.state.bounds;
		if (!b) return;
		var pad = 2;
		ui.cam.x = clamp(ui.cam.x, b.x0 - pad, b.x1 + pad);
		ui.cam.y = clamp(ui.cam.y, b.y0 - pad, b.y1 + pad);
	}

	function frameBoard() {
		var b = ui.state && ui.state.bounds;
		if (!b) {
			ui.cam.x = 0; ui.cam.y = 0; ui.cam.zoom = 1;
			return;
		}
		ui.cam.x = (b.x0 + b.x1) / 2;
		ui.cam.y = (b.y0 + b.y1) / 2;
		var w = (b.x1 - b.x0 + 2) * BASE_CELL;
		var h = (b.y1 - b.y0 + 2) * BASE_CELL;
		ui.cam.zoom = levelForFit(Math.min((ui.metrics.cssW - panelInsetX()) / w, ui.metrics.cssH / h));
	}

	function updateZoomLabel() {
		if (els.zoomLabel) els.zoomLabel.textContent = ZOOM_LABELS[zoomIndex()] || Math.round(ui.cam.zoom * 100) + '%';
	}

	/* ------------------------------------------------------------- scene --- */

	/*
	 * Fortress outlines are permanent. A segment, once drawn between two of a
	 * player's dots, is never moved, re-paired or erased: an enclosure keeps
	 * exactly the shape it had when it was first drawn. New captures only ever
	 * *add* segments around the cells that were just claimed, and may attach to
	 * the existing outline (a fully used dot, with two segments already, just
	 * becomes a joint between the old contour and the new one).
	 *
	 * A segment is a candidate when its two ends are dots of the owner no more
	 * than one cell apart (straight or diagonal) and the freshly claimed cells
	 * sit on exactly one side of it. Per-region border logic keeps a wall that
	 * is shared by two enclosures from being treated as "inside" and stitching
	 * them together with diagonals. When several candidates compete for a dot,
	 * straight segments win over diagonals, so a contour uses as many dots as
	 * it can without ever bending through a diagonal shortcut.
	 */

	function edgeKey(a, b) { return a < b ? a + '|' + b : b + '|' + a; }

	function outlineCandidates(state, owner, touch) {
		var V = new Map();
		state.dots.forEach(function (v, k) {
			if (v !== owner) return;
			var p = E.parseKey(k);
			V.set(k, { x: p[0], y: p[1] });
		});
		if (!V.size) return [];

		var cells = [];
		state.claimed.forEach(function (v, k) { if (v === owner) cells.push(k); });
		if (!cells.length) return [];
		var cellSet = new Set(cells);
		var comp = new Map();
		var compCount = 0;
		var step4 = [[1, 0], [-1, 0], [0, 1], [0, -1]];
		for (var c0 = 0; c0 < cells.length; c0++) {
			if (comp.has(cells[c0])) continue;
			var q = [cells[c0]];
			comp.set(cells[c0], compCount);
			while (q.length) {
				var cur = q.pop();
				var cp = E.parseKey(cur);
				for (var s = 0; s < 4; s++) {
					var mk = E.key(cp[0] + step4[s][0], cp[1] + step4[s][1]);
					if (cellSet.has(mk) && !comp.has(mk)) {
						comp.set(mk, compCount);
						q.push(mk);
					}
				}
			}
			compCount++;
		}
		function inComp(nx, ny, index) {
			var k = E.key(nx, ny);
			return comp.has(k) && comp.get(k) === index;
		}
		function onSomeBorder(x, y, dx, dy) {
			for (var index = 0; index < compCount; index++) {
				var hit;
				if (dy === 0) {
					hit = (inComp(x, y - 1, index) || inComp(x + dx, y - 1, index)) !==
						(inComp(x, y + 1, index) || inComp(x + dx, y + 1, index));
				} else if (dx === 0) {
					hit = (inComp(x - 1, y, index) || inComp(x - 1, y + dy, index)) !==
						(inComp(x + 1, y, index) || inComp(x + 1, y + dy, index));
				} else {
					hit = inComp(x + dx, y, index) !== inComp(x, y + dy, index);
				}
				if (hit) return true;
			}
			return false;
		}
		function touches(touch, x, y, dx, dy) {
			if (dy === 0) {
				return touch.has(E.key(x, y - 1)) || touch.has(E.key(x + dx, y - 1)) ||
					touch.has(E.key(x, y + 1)) || touch.has(E.key(x + dx, y + 1));
			} else if (dx === 0) {
				return touch.has(E.key(x - 1, y)) || touch.has(E.key(x - 1, y + dy)) ||
					touch.has(E.key(x + 1, y)) || touch.has(E.key(x + 1, y + dy));
			}
			return touch.has(E.key(x + dx, y)) || touch.has(E.key(x, y + dy));
		}

		var dirs = [[1, 0], [0, 1], [1, 1], [-1, 1]];
		var seen = new Set();
		var cands = [];
		V.forEach(function (o) {
			for (var d = 0; d < dirs.length; d++) {
				var dx = dirs[d][0], dy = dirs[d][1];
				var nk = E.key(o.x + dx, o.y + dy);
				if (!V.has(nk)) continue;
				if (!onSomeBorder(o.x, o.y, dx, dy)) continue;
				var a = E.key(o.x, o.y);
				var ek = edgeKey(a, nk);
				if (seen.has(ek)) continue;
				seen.add(ek);
				if (!touches(touch, o.x, o.y, dx, dy)) continue;
				var b = V.get(nk);
				cands.push({ ax: o.x, ay: o.y, bx: b.x, by: b.y, owner: owner });
			}
		});
		return cands;
	}

	/*
	 * Greedily add the candidate segments to `edges`, never touching what is
	 * already there. Existing segments seed the per-dot degree: a dot that
	 * already carries two segments becomes a junction when a new enclosure
	 * attaches to it (the old contour keeps its exact shape, the new line just
	 * meets it), while a freshly drawn dot still takes at most two segments so
	 * new contours stay simple.
	 *
	 * Straight segments are all placed first; diagonals come second and one is
	 * dropped when its ends are already joined through a shared dot by two
	 * straight segments. That is the corner "shortcut": without the check the
	 * contour would fill the right angle with an extra diagonal instead of
	 * running through the corner dot.
	 *
	 * Two guarantees are layered on top. A segment that merely lies across a
	 * still free dot is rerouted through it, so the contour carries as many
	 * dots as possible; and the closing pass never leaves an end hanging — it
	 * will even take a corner-cutting segment as a last resort, because a
	 * finished loop is always better than a dead-end stub.
	 */
	function extendOutline(state, owner, touch, edges) {
		var cands = outlineCandidates(state, owner, touch);
		if (!cands.length) return;

		/* every dot of the owner, so the closing pass can reach any neighbour */
		var ownerDots = new Set();
		state.dots.forEach(function (v, k) { if (v === owner) ownerDots.add(k); });

		var used = new Set();
		var deg = new Map();
		var adj = new Map();
		function bump(k) { deg.set(k, (deg.get(k) || 0) + 1); }
		function link(a, b) {
			if (!adj.has(a)) adj.set(a, new Set());
			if (!adj.has(b)) adj.set(b, new Set());
			adj.get(a).add(b); adj.get(b).add(a);
		}
		for (var i = 0; i < edges.length; i++) {
			if (edges[i].owner !== owner) continue;
			var ea = E.key(edges[i].ax, edges[i].ay);
			var eb = E.key(edges[i].bx, edges[i].by);
			var ek0 = edgeKey(ea, eb);
			if (used.has(ek0)) continue;
			used.add(ek0); bump(ea); bump(eb); link(ea, eb);
		}
		var seedDeg = new Map(deg);
		function limit(k) { return (seedDeg.get(k) || 0) > 0 ? 3 : 2; }

		var neighbors = new Map();
		function ensure(k) { if (!neighbors.has(k)) neighbors.set(k, []); }
		var candSeen = new Set();
		for (var c = 0; c < cands.length; c++) {
			var cd = cands[c];
			var ca = E.key(cd.ax, cd.ay);
			var cb = E.key(cd.bx, cd.by);
			var ekc = edgeKey(ca, cb);
			if (candSeen.has(ekc)) continue;
			candSeen.add(ekc);
			ensure(ca); ensure(cb);
			var ortho = (cd.ax === cd.bx || cd.ay === cd.by);
			neighbors.get(ca).push({ k: cb, ortho: ortho });
			neighbors.get(cb).push({ k: ca, ortho: ortho });
		}

		var order = [];
		neighbors.forEach(function (_, k) { order.push(k); });
		order.sort(function (a, b) { return neighbors.get(a).length - neighbors.get(b).length; });

		/*
		 * Guard against "empty" enclosures. A segment whose ends are already
		 * joined by a path closes a loop; if that loop holds no dot at all it
		 * would show as a locked pocket with nothing inside (a bare triangle
		 * between three dots). Such a segment is simply not drawn, so the
		 * outline stays open instead of boxing in an empty sliver.
		 */
		function connected(a, b) {
			if (a === b) return true;
			var seen = new Set([a]);
			var stack = [a];
			while (stack.length) {
				var cur = stack.pop();
				var nb = adj.get(cur);
				if (!nb) continue;
				var hit = false;
				nb.forEach(function (n) {
					if (n === b) hit = true;
					else if (!seen.has(n)) { seen.add(n); stack.push(n); }
				});
				if (hit) return true;
			}
			return false;
		}

		function neighborList(k) {
			var nb = adj.get(k);
			if (!nb || !nb.size) return [];
			var p = E.parseKey(k);
			var arr = [];
			nb.forEach(function (n) { arr.push(n); });
			arr.sort(function (x, y) {
				var qx = E.parseKey(x), qy = E.parseKey(y);
				return Math.atan2(qx[1] - p[1], qx[0] - p[0]) -
					Math.atan2(qy[1] - p[1], qy[0] - p[0]);
			});
			return arr;
		}

		/*
		 * Neighbour of `cur` reached by turning clockwise from the direction
		 * cur->target. `target` need not be an actual neighbour (the edge being
		 * tested is still virtual), only a direction.
		 */
		function clockwiseNext(cur, target) {
			var arr = neighborList(cur);
			if (!arr.length) return null;
			var pc = E.parseKey(cur), pt = E.parseKey(target);
			var ta = Math.atan2(pt[1] - pc[1], pt[0] - pc[0]);
			var best = null, bestDelta = Infinity;
			for (var i = 0; i < arr.length; i++) {
				var pn = E.parseKey(arr[i]);
				var na = Math.atan2(pn[1] - pc[1], pn[0] - pc[0]);
				var d = ta - na;
				if (d <= 1e-9) d += Math.PI * 2;
				if (d < bestDelta) { bestDelta = d; best = arr[i]; }
			}
			return best;
		}

		/* Walk the face bordering directed edge a->b; returns its node cycle. */
		function traceFace(a, b) {
			var prev = a, cur = b, nodes = [a, b], guard = 0;
			while (guard++ < 20000) {
				var nxt = clockwiseNext(cur, prev);
				if (nxt === null) return null;
				nodes.push(nxt);
				if (nxt === a) return nodes;
				prev = cur; cur = nxt;
			}
			return null;
		}

		function polygonArea(nodes) {
			var area = 0;
			for (var i = 0; i < nodes.length; i++) {
				var p = E.parseKey(nodes[i]);
				var q = E.parseKey(nodes[(i + 1) % nodes.length]);
				area += p[0] * q[1] - q[0] * p[1];
			}
			return area / 2;
		}

		function polygonHasDot(nodes) {
			if (nodes.length < 4) return false;
			var on = new Set(nodes);
			var pts = [];
			var minX = Infinity, maxX = -Infinity, minY = Infinity, maxY = -Infinity;
			for (var i = 0; i < nodes.length; i++) {
				var pt = E.parseKey(nodes[i]);
				pts.push(pt);
				if (pt[0] < minX) minX = pt[0];
				if (pt[0] > maxX) maxX = pt[0];
				if (pt[1] < minY) minY = pt[1];
				if (pt[1] > maxY) maxY = pt[1];
			}
			var found = false;
			state.dots.forEach(function (v, k) {
				if (found || on.has(k)) return;
				var p = E.parseKey(k);
				if (p[0] < minX || p[0] > maxX || p[1] < minY || p[1] > maxY) return;
				var inside = false;
				for (var a = 0, b = pts.length - 1; a < pts.length; b = a++) {
					var xi = pts[a][0], yi = pts[a][1], xj = pts[b][0], yj = pts[b][1];
					if (((yi > p[1]) !== (yj > p[1])) &&
						(p[0] < (xj - xi) * (p[1] - yi) / (yj - yi) + xi)) inside = !inside;
				}
				if (inside) found = true;
			});
			return found;
		}

		/* True when segment a-b would close a bounded loop with no dot in it. */
		function makesEmptyPocket(a, b) {
			if (!connected(a, b)) return false;
			var f1 = traceFace(a, b);
			if (f1 && polygonArea(f1) > 0 && !polygonHasDot(f1)) return true;
			var f2 = traceFace(b, a);
			if (f2 && polygonArea(f2) > 0 && !polygonHasDot(f2)) return true;
			return false;
		}

		var addedKeys = new Set();
		function addEdgeRaw(from, to) {
			var ek = edgeKey(from, to);
			if (used.has(ek)) return false;
			if (makesEmptyPocket(from, to)) return false;
			used.add(ek); bump(from); bump(to); link(from, to); addedKeys.add(ek);
			var p1 = E.parseKey(from), p2 = E.parseKey(to);
			edges.push({ ax: p1[0], ay: p1[1], bx: p2[0], by: p2[1], owner: owner });
			return true;
		}
		function tryAdd(from, to) {
			if ((deg.get(from) || 0) >= limit(from)) return false;
			if ((deg.get(to) || 0) >= limit(to)) return false;
			return addEdgeRaw(from, to);
		}
		function removeEdge(from, to) {
			var ek = edgeKey(from, to);
			if (!used.has(ek)) return false;
			used.delete(ek); addedKeys.delete(ek);
			var na = adj.get(from); if (na) na.delete(to);
			var nb = adj.get(to); if (nb) nb.delete(from);
			deg.set(from, Math.max(0, (deg.get(from) || 1) - 1));
			deg.set(to, Math.max(0, (deg.get(to) || 1) - 1));
			var p1 = E.parseKey(from), p2 = E.parseKey(to);
			for (var k = edges.length - 1; k >= 0; k--) {
				var e = edges[k];
				if (e.owner !== owner) continue;
				if ((e.ax === p1[0] && e.ay === p1[1] && e.bx === p2[0] && e.by === p2[1]) ||
					(e.ax === p2[0] && e.ay === p2[1] && e.bx === p1[0] && e.by === p1[1])) {
					edges.splice(k, 1);
					break;
				}
			}
			return true;
		}

		/*
		 * Include as many dots as possible. When a drawn segment `a—b` lies
		 * across a free owner dot `m` (m is adjacent to both ends and both
		 * `a—m` and `m—b` are border candidates), replace `a—b` by the two
		 * segments through `m`. The dot `m` joins the outline and nothing is
		 * left dangling, because `a` and `b` keep their degree and `m` gets
		 * exactly two segments. Only segments drawn in this capture are moved,
		 * so already finished contours are never touched.
		 */
		function maximizeStep() {
			var list = [];
			addedKeys.forEach(function (ek) { list.push(ek); });
			for (var i = 0; i < list.length; i++) {
				var ek = list[i];
				if (!used.has(ek)) continue;
				var bar = ek.indexOf('|');
				var a = ek.slice(0, bar), b = ek.slice(bar + 1);
				var pa = E.parseKey(a), pb = E.parseKey(b);
				var found = null;
				for (var dx = -1; dx <= 1 && !found; dx++) {
					for (var dy = -1; dy <= 1; dy++) {
						if (!dx && !dy) continue;
						var m = E.key(pa[0] + dx, pa[1] + dy);
						if (m === a || m === b) continue;
						if (!ownerDots.has(m)) continue;
						if ((deg.get(m) || 0) !== 0) continue;
						var mp = E.parseKey(m);
						if (Math.abs(mp[0] - pb[0]) > 1 || Math.abs(mp[1] - pb[1]) > 1) continue;
						if (mp[0] === pb[0] && mp[1] === pb[1]) continue;
						var am = edgeKey(a, m), mb = edgeKey(m, b);
						if (!candSeen.has(am) || !candSeen.has(mb)) continue;
						if (used.has(am) || used.has(mb)) continue;
						found = m; break;
					}
				}
				if (found && (makesEmptyPocket(a, found) || makesEmptyPocket(found, b))) found = null;
				if (found) {
					removeEdge(a, b);
					addEdgeRaw(a, found);
					addEdgeRaw(found, b);
					return true;
				}
			}
			return false;
		}

		function ordered(from, orthoOnly) {
			return neighbors.get(from).slice().filter(function (n) {
				return orthoOnly ? n.ortho : true;
			}).sort(function (a, b) {
				if (a.ortho !== b.ortho) return a.ortho ? -1 : 1;
				return (deg.get(a.k) || 0) - (deg.get(b.k) || 0);
			});
		}

		/* straight segments first: a corner never takes a diagonal shortcut */
		for (var u = 0; u < order.length; u++) {
			var oFrom = order[u];
			var onb = ordered(oFrom, true);
			for (var oj = 0; oj < onb.length; oj++) tryAdd(oFrom, onb[oj].k);
		}
		/* then diagonals, skipping the ones that only cut a drawn corner */
		for (var v = 0; v < order.length; v++) {
			var dFrom = order[v];
			var dnb = ordered(dFrom, false);
			for (var dj = 0; dj < dnb.length; dj++) {
				if (dnb[dj].ortho) continue;
				var to = dnb[dj].k;
				if (cutsCorner(dFrom, to, adj)) continue;
				tryAdd(dFrom, to);
			}
		}

		/*
		 * Close every open end. A dot with a single segment would be a line
		 * sticking out into nothing, so it is linked to an adjacent dot of the
		 * same owner — a border candidate when possible, otherwise any
		 * neighbour, even past the usual cap (which can make a four-way
		 * junction). When the only closing segment would cut a corner, the
		 * shortcut drawn in this very capture is dropped and the loose end is
		 * joined to the dot beyond it instead, so no dot is left dangling.
		 */
		function rewireEnd(end, pe) {
			for (var ddx = -1; ddx <= 1; ddx++) {
				for (var ddy = -1; ddy <= 1; ddy++) {
					if (!ddx && !ddy) continue;
					var to = E.key(pe[0] + ddx, pe[1] + ddy);
					if (!ownerDots.has(to)) continue;
					if (used.has(edgeKey(end, to))) continue;
					var na = adj.get(end);
					if (!na) continue;
					var mid = null;
					na.forEach(function (m) {
						if (mid || m === to) return;
						var nm = adj.get(m);
						if (!nm || !nm.has(to)) return;
						if ((deg.get(m) || 0) < 3) return;          /* it must stay a corner */
						if (!addedKeys.has(edgeKey(m, to))) return; /* only this capture's segment */
						mid = m;
					});
					if (!mid) continue;
					if (makesEmptyPocket(end, to)) continue;
					removeEdge(mid, to);
					return addEdgeRaw(end, to);
				}
			}
			return false;
		}

		var guard = 0, progress = true;
		while (progress && guard++ < 4000) {
			progress = false;
			if (maximizeStep()) progress = true;
			var verts = [];
			adj.forEach(function (_, k) { verts.push(k); });
			for (var q = 0; q < verts.length; q++) {
				var end = verts[q];
				if ((deg.get(end) || 0) !== 1) continue;
				var pe = E.parseKey(end);
				var best = null, bestRank = 99;
				for (var ddx = -1; ddx <= 1; ddx++) {
					for (var ddy = -1; ddy <= 1; ddy++) {
						if (!ddx && !ddy) continue;
						var nk = E.key(pe[0] + ddx, pe[1] + ddy);
						if (!ownerDots.has(nk)) continue;
						var ekc = edgeKey(end, nk);
						if (used.has(ekc)) continue;
						if (makesEmptyPocket(end, nk)) continue;
						/*
						 * A corner-cutting segment is allowed here as a last
						 * resort: a dangling stub is worse than a small closing
						 * triangle. The rank penalty keeps it behind every
						 * clean closing edge, so routing through a free dot or
						 * a non-cutting segment is always preferred.
						 */
						var cutC = cutsCorner(end, nk, adj);
						var cd = deg.get(nk) || 0;
						var isCand = candSeen.has(ekc);
						var ortho = (ddx === 0 || ddy === 0);
						var rank = (cd === 1 ? 0 : (cd === 2 ? 1 : (cd === 3 ? 2 : 4))) +
							(ortho ? 0 : 0.5) + (isCand ? 0 : 1.5) + (cutC ? 3 : 0);
						if (rank < bestRank) { bestRank = rank; best = nk; }
					}
				}
				if (best !== null) {
					addEdgeRaw(end, best);
					progress = true;
					continue;
				}
				if (rewireEnd(end, pe)) progress = true;
			}
		}

		/*
		 * Safety net for the rare case of a lone two-dot stub whose ends have
		 * no other owner neighbour to close onto: drop it (only segments made
		 * in this capture) so the board is never left with a dangling end.
		 */
		var pruned = true;
		while (pruned) {
			pruned = false;
			var singles = [];
			adj.forEach(function (_, k) { if ((deg.get(k) || 0) === 1) singles.push(k); });
			for (var s = 0; s < singles.length; s++) {
				var stub = singles[s];
				var nb = adj.get(stub);
				if (!nb || nb.size !== 1) continue;
				var other = null;
				nb.forEach(function (p) { other = p; });
				if (other !== null && addedKeys.has(edgeKey(stub, other))) {
					removeEdge(stub, other);
					pruned = true;
					break;
				}
			}
		}
	}

	/* true when `a` and `b` are already joined through a shared dot by two segments */
	function cutsCorner(a, b, adj) {
		var na = adj.get(a);
		if (!na) return false;
		var hit = false;
		na.forEach(function (mid) {
			if (mid === b || hit) return;
			var nm = adj.get(mid);
			if (nm && nm.has(b)) hit = true;
		});
		return hit;
	}

	function extendScene(player, claimed) {
		if (!claimed || !claimed.length) return;
		var touch = new Set();
		for (var i = 0; i < claimed.length; i++) touch.add(E.key(claimed[i].x, claimed[i].y));
		extendOutline(ui.state, player, touch, ui.scene.edges);
	}

	/* ------------------------------------------------------------- drawing --- */

	function render() {
		if (!ui.ctx || !ui.metrics || !ui.state) return;
		var s = ui.state;
		var pal = ui.palette;
		var ctx = ui.ctx;
		var m = ui.metrics;
		var sc = scale();
		var cx = viewCenterX(), cy = m.cssH / 2;

		ctx.setTransform(m.dpr, 0, 0, m.dpr, 0, 0);
		ctx.clearRect(0, 0, m.cssW, m.cssH);
		ctx.fillStyle = pal.boardPaper;
		ctx.fillRect(0, 0, m.cssW, m.cssH);

		function sx(wx) { return cx + (wx - ui.cam.x) * sc; }
		function sy(wy) { return cy + (wy - ui.cam.y) * sc; }
		var left = ui.cam.x - cx / sc, right = ui.cam.x + (m.cssW - cx) / sc;
		var top = ui.cam.y - cy / sc, bottom = ui.cam.y + (m.cssH - cy) / sc;

		/* A bounded field defines where the grid is drawn and where play stops. */
		var b = s.bounds;
		var gL = b ? Math.max(left, b.x0) : left;
		var gR = b ? Math.min(right, b.x1) : right;
		var gT = b ? Math.max(top, b.y0) : top;
		var gB = b ? Math.min(bottom, b.y1) : bottom;

		/* grid, with an adaptive step so lines never crowd together */
		var step = 1;
		while (sc * step < 14) step *= 2;
		ctx.lineWidth = 1;
		ctx.strokeStyle = pal.grid;
		var gx0 = Math.ceil(gL / step) * step;
		for (var gx = gx0; gx <= gR; gx += step) {
			var X = Math.round(sx(gx)) + 0.5;
			ctx.beginPath(); ctx.moveTo(X, sy(gT)); ctx.lineTo(X, sy(gB)); ctx.stroke();
		}
		var gy0 = Math.ceil(gT / step) * step;
		for (var gy = gy0; gy <= gB; gy += step) {
			var Y = Math.round(sy(gy)) + 0.5;
			ctx.beginPath(); ctx.moveTo(sx(gL), Y); ctx.lineTo(sx(gR), Y); ctx.stroke();
		}
		/* the edge of the sheet */
		if (b) {
			ctx.strokeStyle = pal.gridBold;
			ctx.lineWidth = 2;
			ctx.strokeRect(sx(b.x0), sy(b.y0), (b.x1 - b.x0) * sc, (b.y1 - b.y0) * sc);
		}
		/* fortress outlines (30% thinner than before) */
		ctx.lineCap = 'round';
		ctx.lineJoin = 'round';
		ctx.lineWidth = Math.max(1.05, sc * 0.077);
		for (var i = 0; i < ui.scene.edges.length; i++) {
			var e = ui.scene.edges[i];
			/* A fortress outline is drawn in the muted colour of the side it
			   enclosed: blue enclosing red draws dark red, and vice versa. */
			ctx.strokeStyle = e.owner === 1 ? pal.p2Captured : pal.p1Captured;
			ctx.beginPath();
			ctx.moveTo(sx(e.ax), sy(e.ay));
			ctx.lineTo(sx(e.bx), sy(e.by));
			ctx.stroke();
		}

		/* dots */
		var margin = sc * 1.5;
		ui.state.dots.forEach(function (v, k) {
			var p = E.parseKey(k);
			var px = sx(p[0]), py = sy(p[1]);
			if (px < -margin || px > m.cssW + margin || py < -margin || py > m.cssH + margin) return;
			if (v === 1 || v === 2) {
				ctx.fillStyle = v === 1 ? pal.p1 : pal.p2;
			} else {
				/*
				 * An enclosed dot keeps the muted colour of the side it was
				 * taken from: captured red dots are dark red, captured blue
				 * dots dark blue.
				 */
				var own = E.ownerOf(v);
				ctx.fillStyle = own === 1 ? pal.p1Captured : pal.p2Captured;
			}
			ctx.beginPath(); ctx.arc(px, py, sc * 0.15, 0, TAU); ctx.fill();
		});

		/* last move — deliberately faint */
		if (s.lastMove) {
			var lx = sx(s.lastMove.x), ly = sy(s.lastMove.y);
			ctx.globalAlpha = 0.35;
			ctx.strokeStyle = pal.accent;
			ctx.lineWidth = Math.max(1, sc * 0.05);
			ctx.beginPath(); ctx.arc(lx, ly, Math.max(3, sc * 0.27), 0, TAU); ctx.stroke();
			ctx.globalAlpha = 1;
		}

		/* hover preview + guide lines */
		if (ui.hover && !isLocked()) {
			var hx = sx(ui.hover.x), hy = sy(ui.hover.y);
			ctx.globalAlpha = 0.4;
			ctx.strokeStyle = pal.gridBold;
			ctx.lineWidth = 1;
			ctx.beginPath();
			ctx.moveTo(0, hy + 0.5); ctx.lineTo(m.cssW, hy + 0.5);
			ctx.moveTo(hx + 0.5, 0); ctx.lineTo(hx + 0.5, m.cssH);
			ctx.stroke();
			ctx.globalAlpha = 1;
			if (E.canPlace(s, ui.hover.x, ui.hover.y)) {
				var turn = s.turn;
				var hc = turn === 1 ? pal.p1 : pal.p2;
				ctx.globalAlpha = 0.32;
				ctx.fillStyle = hc;
				ctx.beginPath(); ctx.arc(hx, hy, sc * 0.15, 0, TAU); ctx.fill();
				ctx.globalAlpha = 1;
				ctx.strokeStyle = hc;
				ctx.lineWidth = 1.5;
				ctx.beginPath(); ctx.arc(hx, hy, sc * 0.32, 0, TAU); ctx.stroke();
			} else {
				drawCross(ctx, hx, hy, sc * 0.24, pal.danger);
			}
		}

		/* keyboard cursor */
		if (ui.keyboard && document.activeElement === els.canvas) {
			var kx = sx(ui.cursor.x), ky = sy(ui.cursor.y);
			ctx.strokeStyle = pal.accent;
			ctx.lineWidth = 2;
			ctx.beginPath(); ctx.arc(kx, ky, Math.max(4, sc * 0.34), 0, TAU); ctx.stroke();
		}

		if (ui.flash) {
			var fx = sx(ui.flash.x), fy = sy(ui.flash.y);
			drawCross(ctx, fx, fy, sc * 0.26, pal.danger);
		}
	}

	function drawCross(ctx, cx, cy, r, color) {
		ctx.strokeStyle = color;
		ctx.lineWidth = 2.5;
		ctx.lineCap = 'round';
		ctx.beginPath();
		ctx.moveTo(cx - r, cy - r); ctx.lineTo(cx + r, cy + r);
		ctx.moveTo(cx + r, cy - r); ctx.lineTo(cx - r, cy + r);
		ctx.stroke();
	}

	/* --------------------------------------------------------------- state --- */

	function isLocked() {
		return ui.ended || !ui.started || (ui.mode === 'bot' && (ui.state.turn === 2 || ui.thinking));
	}

	function pushHistory() {
		ui.history.push({
			state: E.clone(ui.state),
			scene: { edges: ui.scene.edges.slice() },
			ended: ui.ended
		});
	}

	function restore(entry) {
		ui.state = entry.state;
		ui.scene = entry.scene;
		ui.ended = entry.ended;
	}

	function commitMove(x, y) {
		pushHistory();
		var player = ui.state.turn;
		var res = E.place(ui.state, x, y);
		if (!res.ok) { ui.history.pop(); return; }
		if (ui.mode === 'bot' && res.player === 2) ui.botMoves += 1;
		/* Count the computer's fruitless moves so a repeating deadlock is
		   broken instead of running forever; any capture resets the count. */
		if (res.capturedCount > 0) ui.botQuiet = 0;
		else if (ui.mode === 'bot' && res.player === 2) ui.botQuiet += 1;
		ui.hover = null;
		ui.cursor.x = x; ui.cursor.y = y;
		extendScene(res.player, res.claimed);
		if (ui.timeLimit && !ui.deadline) startClock();
		announce(res, player);
		render();
		updatePanel();
		if (ui.mode === 'bot' && ui.state.turn === 2) scheduleBot();
	}

	function announce(res, player) {
		var text = NAMES[player] + ' поставили точку.';
		if (res.capturedCount > 0) {
			text += ' Захвачено: ' + res.capturedCount + ' ' + pointsWord(res.capturedCount) + '.';
		}
		text += ' Ход: ' + NAMES[ui.state.turn] + '.';
		els.live.textContent = text;
	}

	/* ---------------------------------------------------------------- clock --- */

	function nowMs() { return (window.performance && performance.now) ? performance.now() : Date.now(); }

	function formatClock(ms) {
		var total = Math.ceil(ms / 1000);
		var h = Math.floor(total / 3600);
		var m = Math.floor((total % 3600) / 60);
		var s = total % 60;
		if (h > 0) return h + ':' + (m < 10 ? '0' : '') + m + ':' + (s < 10 ? '0' : '') + s;
		return m + ':' + (s < 10 ? '0' : '') + s;
	}

	function updateTimerLabel() {
		if (!els.timeLeft) return;
		var show = ui.timeLimit > 0;
		els.timeLeft.hidden = !show;
		if (els.timeSep) els.timeSep.hidden = !show;
		if (!show) return;
		var left;
		if (ui.ended) left = 0;
		else if (ui.deadline) left = Math.max(0, ui.deadline - nowMs());
		else left = ui.timeLimit * 1000;
		els.timeLeft.textContent = formatClock(left);
		els.timeLeft.classList.toggle('is-low', !ui.ended && left <= 5000);
	}

	function stopClock() {
		if (ui.clockTimer) { window.clearInterval(ui.clockTimer); ui.clockTimer = null; }
	}

	/*
	 * A tiny seconds counter in the turn badge, shown only while the computer
	 * is thinking, so the wait is visible rather than silent.
	 */
	function stopThinkTimer() {
		if (ui.thinkTimer) { window.clearInterval(ui.thinkTimer); ui.thinkTimer = null; }
	}

	function syncThinkTimer() {
		if (!els.turnClock) return;
		var show = ui.mode === 'bot' && ui.thinking && !ui.ended;
		if (!show) {
			els.turnClock.hidden = true;
			stopThinkTimer();
			return;
		}
		els.turnClock.hidden = false;
		if (!ui.thinkTimer) {
			ui.thinkStart = nowMs();
			els.turnClock.textContent = '0 с';
			ui.thinkTimer = window.setInterval(function () {
				if (!ui.thinking || ui.ended) {
					stopThinkTimer();
					if (els.turnClock) els.turnClock.hidden = true;
					return;
				}
				els.turnClock.textContent = Math.floor((nowMs() - ui.thinkStart) / 1000) + ' с';
			}, 200);
		}
	}

	/* The clock starts on the first move, so choosing the setting is not timed. */
	function startClock() {
		stopClock();
		if (!ui.timeLimit || ui.ended) return;
		ui.deadline = nowMs() + ui.timeLimit * 1000;
		ui.clockTimer = window.setInterval(function () {
			if (ui.ended) { stopClock(); return; }
			updateTimerLabel();
			if (ui.deadline && nowMs() >= ui.deadline) {
				stopClock();
				if (!ui.ended) showResult(null, 'time');
			}
		}, 200);
		updateTimerLabel();
	}

	/* ----------------------------------------------------------- new game --- */

	function boundsForSize(size) {
		var cells = FIELD_SIZES[size];
		if (!cells) return null;
		return { x0: 0, y0: 0, x1: cells, y1: cells };
	}

	function newGame() {
		ui.state = E.createGame({ extraTurn: false, bounds: boundsForSize(ui.size) });
		ui.history = [];
		ui.ended = false;
		ui.thinking = false;
		ui.botRequestId += 1;
		ui.botMoves = 0;
		ui.botQuiet = 0;
		ui.botAlt = false;
		ui.hover = null;
		ui.flash = null;
		ui.keyboard = false;
		ui.scene = { edges: [] };
		ui.deadline = null;
		stopClock();
		var b = ui.state.bounds;
		ui.cursor.x = b ? Math.floor((b.x0 + b.x1) / 2) : 0;
		ui.cursor.y = b ? Math.floor((b.y0 + b.y1) / 2) : 0;
		fit();
		frameBoard();
		updateZoomLabel();
		ui.started = false;
		render();
		updatePanel();
	}

	/* Started from the panel: the board stays frozen until this is pressed, so
	   the settings can be chosen even when the computer moves first. */
	function startGame() {
		if (ui.started && !ui.ended) return;
		newGame();
		ui.started = true;
		if (ui.mode === 'bot' && ui.first === 'bot') ui.state.turn = 2;
		render();
		updatePanel();
		if (ui.mode === 'bot' && ui.first === 'bot') scheduleBot();
	}

	/* --------------------------------------------------------------- panel --- */

	function updatePanel() {
		var s = ui.state;
		els.score1.textContent = s.score[1];
		els.score2.textContent = s.score[2];
		els.captured1.textContent = E.activeCount(s, 1);
		els.captured2.textContent = E.activeCount(s, 2);
		if (els.dotCount) els.dotCount.textContent = 'Точек: ' + (E.activeCount(s, 1) + E.activeCount(s, 2));
		if (els.moveCount) els.moveCount.textContent = 'Ходов: ' + s.moveCount;

		var active = ui.ended ? 0 : s.turn;
		els.card1.classList.toggle('is-active', active === 1);
		els.card2.classList.toggle('is-active', active === 2);

		els.turn.setAttribute('data-player', String(s.turn));
		if (ui.ended) {
			els.turn.classList.remove('is-thinking');
			els.turnText.textContent = 'Партия завершена';
		} else if (ui.thinking) {
			els.turn.classList.add('is-thinking');
			els.turnText.textContent = 'Компьютер думает';
		} else {
			els.turn.classList.remove('is-thinking');
			els.turnText.textContent = 'Ход: ' + NAMES[s.turn];
		}
		syncThinkTimer();

		var bot = ui.mode === 'bot';
		els.difficultySetting.hidden = !bot;
		els.firstSetting.hidden = !bot;
		els.you1.hidden = !bot;
		els.you2.hidden = !bot;
		els.you2.textContent = 'соперник';

		var started = ui.started;
		var inProgress = started && !ui.ended;
		els.startBtn.hidden = inProgress;
		els.undoBtn.hidden = !started;
		els.finishBtn.hidden = !started;
		els.undoBtn.disabled = false;
		els.finishBtn.disabled = false;
		els.canvas.classList.toggle('is-locked', ui.ended || !ui.started);
		els.canvas.classList.toggle('is-thinking', ui.thinking);
		updateZoomLabel();
		updateTimerLabel();
		applyPanelVisibility();
	}

	/* ----------------------------------------------------------------- bot --- */

	/*
	 * The search worker keeps long think times off the UI thread. Several ways
	 * to start it are tried in turn, because some hosts block one or another:
	 *   1. the same-origin file bot-worker.js (works under `script-src 'self'`);
	 *   2. a Blob worker that pulls engine.js in by absolute URL (works when
	 *      separate files are not deployed).
	 * Only if none starts does the search fall back to the main thread.
	 */
	function botWorkerSource() {
		var engineUrl = new URL('engine.js', document.baseURI).href;
		return 'importScripts(' + JSON.stringify(engineUrl) + ');' +
			'self.onmessage=function(ev){' +
			'var d=ev.data||{};' +
			'var s={dots:new Map(d.dots),claimed:new Map(d.claimed),turn:d.turn,score:d.score,' +
			'rules:d.rules,bounds:d.bounds||null,lastMove:d.lastMove||null,moveCount:d.moveCount};' +
			'var m=[];try{' +
			'if((d.count||1)<=1){var b=self.DotsEngine.bestMove(s,d.player,d.options);m=b?[b]:[];}' +
			'else{m=self.DotsEngine.bestMoves(s,d.player,d.options,d.count)||[];}' +
			'}catch(err){m=[];}' +
			'self.postMessage({id:d.id,moves:m});};';
	}

	function stopBotWorker() {
		if (ui.botWorker) { try { ui.botWorker.terminate(); } catch (err) {} ui.botWorker = null; }
		if (ui.botWorkerUrl) { try { URL.revokeObjectURL(ui.botWorkerUrl); } catch (err) {} ui.botWorkerUrl = null; }
	}

	function attachBotWorker(w, kind) {
		ui.botWorker = w;
		ui.botWorkerKind = kind;
		w.onmessage = function (ev) {
			var msg = ev.data || {};
			if (msg.id !== ui.botRequestId) return; /* stale request */
			ui.botPending = null;
			finishBotMove(chooseBotMove(msg.moves));
		};
		w.onerror = function () {
			/* this worker could not run; drop it and try the next option */
			if (ui.botWorker === w) stopBotWorker();
			if (!ui.thinking) return;
			var spawned = spawnBotWorker();
			if (spawned) {
				attachBotWorker(spawned.w, spawned.kind);
				if (ui.botPending) spawned.w.postMessage(ui.botPending);
			} else {
				ui.botWorkerFailed = true;
				runBotSearchCooperative(DIFFICULTY[ui.difficulty] || DIFFICULTY.medium, 1);
			}
		};
	}

	function spawnBotWorker() {
		var kinds = ui.botWorkerKinds || [];
		while (kinds.length) {
			var kind = kinds.shift();
			try {
				if (kind === 'file' && window.Worker) return { w: new Worker('bot-worker.js'), kind: kind };
				if (kind === 'blob' && window.Worker && window.Blob && window.URL && URL.createObjectURL) {
					ui.botWorkerUrl = URL.createObjectURL(new Blob([botWorkerSource()], { type: 'application/javascript' }));
					return { w: new Worker(ui.botWorkerUrl), kind: kind };
				}
			} catch (err) { /* try the next kind */ }
		}
		return null;
	}

	/* Starts the next worker option and re-sends the pending request, if any. */
	function startBotWorker() {
		stopBotWorker();
		var spawned = spawnBotWorker();
		if (!spawned) { ui.botWorkerFailed = true; return null; }
		attachBotWorker(spawned.w, spawned.kind);
		if (ui.botPending) spawned.w.postMessage(ui.botPending);
		return spawned.w;
	}

	function ensureBotWorker() {
		if (ui.botWorker) return ui.botWorker;
		if (ui.botWorkerFailed) return null;
		return startBotWorker();
	}

	/*
	 * The computer normally plays the single best move it has found. When the
	 * anti-repetition valve has tripped, the search returns the top two moves
	 * and the second one is played instead, so a repeating deadlock breaks.
	 */
	function chooseBotMove(list) {
		var alt = ui.botAlt;
		ui.botAlt = false;
		if (!list || !list.length) return null;
		if (alt && list.length > 1) return list[1];
		return list[0];
	}

	function finishBotMove(move) {
		ui.thinking = false;
		if (ui.mode !== 'bot' || ui.ended || ui.state.turn !== 2) { render(); updatePanel(); return; }
		if (!move) { render(); updatePanel(); return; }
		commitMove(move.x, move.y);
	}

	function requestBotMove(preset) {
		var options = {
			timeBudget: preset.timeBudget,
			maxDepth: preset.maxDepth,
			maxMoves: preset.maxMoves,
			rootLimit: preset.rootLimit,
			tacticalScan: preset.tacticalScan,
			captureScan: preset.captureScan
		};
		/* Break a repeating, capture-less deadlock by trying the runner-up. */
		ui.botAlt = ui.botQuiet >= REPEAT_AFTER;
		if (ui.botAlt) ui.botQuiet = 0;
		var count = ui.botAlt ? 2 : 1;
		ui.botRequestId += 1;
		var s = ui.state;
		ui.botPending = {
			id: ui.botRequestId,
			dots: Array.from(s.dots),
			claimed: Array.from(s.claimed),
			turn: s.turn,
			score: { 1: s.score[1], 2: s.score[2] },
			rules: s.rules,
			bounds: s.bounds,
			lastMove: s.lastMove,
			moveCount: s.moveCount,
			player: 2,
			count: count,
			options: options
		};
		var worker = ensureBotWorker();
		if (worker) {
			worker.postMessage(ui.botPending);
			return;
		}
		/* no worker available: cooperative search on the main thread (yields) */
		runBotSearchCooperative(preset, count);
	}

	/*
	 * Runs the search on the main thread but lets the browser breathe between
	 * slices, so panning and zooming keep working even without a web worker.
	 * It searches a clone, so the live board stays untouched while it thinks.
	 */
	function runBotSearchCooperative(preset, count) {
		var options = {
			timeBudget: preset.timeBudget,
			maxDepth: preset.maxDepth,
			maxMoves: preset.maxMoves,
			rootLimit: preset.rootLimit,
			tacticalScan: preset.tacticalScan,
			captureScan: preset.captureScan
		};
		var clone = E.clone(ui.state);
		var gen = (count <= 1) ? E.bestMoveGen(clone, 2, options) : E.bestMovesGen(clone, 2, options, count);
		var reqId = ui.botRequestId;
		function done(res) {
			var value = res.value;
			var list = (count <= 1) ? (value ? [value] : []) : (value || []);
			finishBotMove(chooseBotMove(list));
		}
		/* Hidden tab: nobody needs the UI to breathe, and throttled timers
		   would drag the search out — run it straight through. */
		if (document.hidden) {
			var r;
			do { r = gen.next(); } while (!r.done);
			if (reqId === ui.botRequestId && !ui.ended && ui.mode === 'bot') done(r);
			return;
		}
		function slice() {
			if (reqId !== ui.botRequestId || ui.ended || ui.mode !== 'bot') return;
			var end = nowMs() + 20;
			var res;
			do { res = gen.next(); } while (!res.done && nowMs() < end);
			if (!res.done) { window.setTimeout(slice, 0); return; }
			done(res);
		}
		window.setTimeout(slice, 0);
	}

	function scheduleBot() {
		if (ui.mode !== 'bot' || ui.ended || ui.thinking) return;
		ui.thinking = true;
		updatePanel();
		window.setTimeout(function () {
			if (ui.mode !== 'bot' || ui.ended || ui.state.turn !== 2) {
				ui.thinking = false; render(); updatePanel(); return;
			}
			var preset = DIFFICULTY[ui.difficulty] || DIFFICULTY.medium;
			requestBotMove(preset);
		}, 420);
	}

	/* ------------------------------------------------------------ controls --- */

	function attemptPlace(x, y) {
		if (isLocked()) return;
		if (!E.canPlace(ui.state, x, y)) {
			ui.flash = { x: x, y: y };
			render();
			window.setTimeout(function () { ui.flash = null; render(); }, 320);
			return;
		}
		commitMove(x, y);
	}

	function undo() {
		if (!ui.history.length) return;
		/* The button is always live: undo may interrupt the computer's turn. */
		if (ui.thinking) {
			ui.thinking = false;
			ui.botPending = null;
			ui.botAlt = false;
			ui.botRequestId += 1; /* ignore any reply that is already on its way */
		}
		restore(ui.history.pop());
		if (ui.mode === 'bot') {
			while (ui.state.turn !== 1 && ui.history.length) restore(ui.history.pop());
		}
		ui.ended = false;
		ui.hover = null;
		render();
		updatePanel();
	}

	function centerOnLast() {
		var target = ui.state.lastMove;
		var b = ui.state.bounds;
		var tx = target ? target.x : (b ? (b.x0 + b.x1) / 2 : 0);
		var ty = target ? target.y : (b ? (b.y0 + b.y1) / 2 : 0);
		animateCam(tx, ty, 320);
	}

	function animateCam(tx, ty, duration) {
		var reduced = window.matchMedia && window.matchMedia('(prefers-reduced-motion: reduce)').matches;
		if (reduced) { ui.cam.x = tx; ui.cam.y = ty; clampCamera(); render(); return; }
		var startX = ui.cam.x, startY = ui.cam.y, t0 = performance.now();
		function frame(now) {
			var t = Math.min(1, (now - t0) / duration);
			var e = 1 - Math.pow(1 - t, 3);
			ui.cam.x = startX + (tx - startX) * e;
			ui.cam.y = startY + (ty - startY) * e;
			clampCamera();
			render();
			if (t < 1) requestAnimationFrame(frame);
		}
		requestAnimationFrame(frame);
	}

	function applySettingsUI() {
		Array.prototype.forEach.call(els.modeOpts, function (btn) {
			markOption(btn, btn.getAttribute('data-mode') === ui.mode);
		});
		Array.prototype.forEach.call(els.sizeOpts, function (btn) {
			markOption(btn, btn.getAttribute('data-size') === ui.size);
		});
		Array.prototype.forEach.call(els.difficultyOpts, function (btn) {
			markOption(btn, btn.getAttribute('data-difficulty') === ui.difficulty);
		});
		Array.prototype.forEach.call(els.firstOpts, function (btn) {
			markOption(btn, btn.getAttribute('data-first') === ui.first);
		});
		updateTimeUI();
	}

	/*
	 * The board area (turn + score) appears once the game has started, and the
	 * setup block is shown only when no game is in progress — before the start
	 * and after the end.
	 */
	function applyPanelVisibility() {
		var started = ui.started;
		var inProgress = started && !ui.ended;
		if (els.panelStatus) els.panelStatus.hidden = !started;
		if (els.scoreEl) els.scoreEl.hidden = !started;
		if (els.settingsEl) els.settingsEl.hidden = inProgress;
	}

	/* The displayed value is the pending choice; the timer is only "on" when a
	   numeric value is selected, otherwise the game runs without a limit. */
	function updateTimeUI() {
		if (!els.timeValue) return;
		var unlimited = ui.timeLimit === 0;
		els.timeValue.textContent = formatClock(timeAt(ui.timeIndex) * 1000);
		els.timeStepper.classList.toggle('is-idle', unlimited);
		els.timeNone.classList.toggle('is-active', unlimited);
		els.timeNone.setAttribute('aria-pressed', unlimited ? 'true' : 'false');
	}

	function stepTime(dir) {
		if (dir > 0) {
			ui.timeIndex += 1;
			ui.timeLimit = timeAt(ui.timeIndex);
		} else if (ui.timeIndex > 0) {
			ui.timeIndex -= 1;
			ui.timeLimit = timeAt(ui.timeIndex);
		} else if (ui.timeLimit === 0) {
			/* already at the smallest value: switch the clock on */
			ui.timeLimit = timeAt(0);
		} else {
			return;
		}
		saveSetting('dots:timeIndex', String(ui.timeIndex));
		saveSetting('dots:time', String(ui.timeLimit));
		applySettingsUI();
		newGame();
	}

	function clearTimeLimit() {
		if (ui.timeLimit === 0) return;
		ui.timeLimit = 0;
		saveSetting('dots:time', '0');
		applySettingsUI();
		newGame();
	}

	/* --------------------------------------------------------------- panel --- */

	function applyPanelUI() {
		document.body.classList.toggle('panel-hidden', ui.panelHidden);
		if (!els.panelBtn) return;
		els.panelBtn.setAttribute('aria-pressed', ui.panelHidden ? 'true' : 'false');
		var label = ui.panelHidden ? 'Показать панель' : 'Скрыть панель';
		els.panelBtn.setAttribute('aria-label', label);
		els.panelBtn.setAttribute('title', label);
	}

	function togglePanel() {
		ui.panelHidden = !ui.panelHidden;
		applyPanelUI();
		clampCamera();
		render();
	}

	function markOption(btn, on) {
		btn.classList.toggle('is-active', on);
		btn.setAttribute('aria-pressed', on ? 'true' : 'false');
	}

	/* -------------------------------------------------------------- dialogs --- */

	function showResult(winner, reason) {
		ui.ended = true;
		ui.thinking = false;
		ui.botRequestId += 1;
		stopClock();
		var s = ui.state;
		var s1 = s.score[1], s2 = s.score[2];
		var title, lead;

		if (reason === 'resign') {
			title = NAMES[winner] + ' побеждают';
			lead = NAMES[winner === 1 ? 2 : 1] + ' сдались.';
			els.resultBadge.innerHTML = BADGE_TROPHY;
		} else if (s1 === s2) {
			title = 'Ничья';
			lead = 'Поймано равное число точек: ' + s1 + ' : ' + s2 + '.';
			els.resultBadge.innerHTML = BADGE_HANDSHAKE;
		} else {
			var w = s1 > s2 ? 1 : 2;
			var wn = w === 1 ? s1 : s2;
			title = NAMES[w] + ' побеждают';
			lead = NAMES[w] + ' взяли в плен ' + wn + ' ' + pointsWord(wn) + ' соперника.';
			els.resultBadge.innerHTML = BADGE_TROPHY;
		}
		if (reason === 'time') lead = 'Время вышло. ' + lead;

		els.resultTitle.textContent = title;
		els.resultLead.textContent = lead;
		els.resultName1.textContent = NAMES[1];
		els.resultName2.textContent = NAMES[2];
		els.resultScore1.textContent = s1;
		els.resultScore2.textContent = s2;
		render();
		updatePanel();
		if (!els.resultDialog.open) els.resultDialog.showModal();
	}

	var confirmCallback = null;

	function askConfirm(opts) {
		els.confirmTitle.textContent = opts.title;
		els.confirmLead.textContent = opts.lead;
		els.confirmOk.textContent = opts.okLabel;
		els.confirmOk.className = 'btn ' + (opts.danger ? 'btn--danger-solid' : 'btn--primary');
		confirmCallback = opts.onOk;
		els.confirmDialog.showModal();
	}

	/* ------------------------------------------------------------- theme --- */

	function initTheme() {
		var stored = null;
		try { stored = localStorage.getItem('dots:theme'); } catch (err) { stored = null; }
		if (!stored) {
			stored = window.matchMedia && window.matchMedia('(prefers-color-scheme: dark)').matches ? 'dark' : 'light';
		}
		document.documentElement.setAttribute('data-theme', stored);
		ui.palette = readPalette();
		updateThemeButton();
	}

	function toggleTheme() {
		var next = document.documentElement.getAttribute('data-theme') === 'dark' ? 'light' : 'dark';
		setTheme(next);
		try { localStorage.setItem('dots:theme', next); } catch (err) {}
	}

	/* ------------------------------------------------------------- events --- */

	function updateHover(evt) {
		var p = localPoint(evt);
		var node = nodeAtScreen(p.x, p.y);
		if (node === null) {
			if (ui.hover) { ui.hover = null; render(); }
			return;
		}
		if (!ui.hover || ui.hover.x !== node.x || ui.hover.y !== node.y) {
			ui.hover = node;
			render();
		}
	}

	function bindEvents() {
		els.canvas.addEventListener('pointerdown', function (evt) {
			els.canvas.focus({ preventScroll: true });
			ui.keyboard = false;
			ui.hover = null;
			try { els.canvas.setPointerCapture(evt.pointerId); } catch (err) {}
			ui.pointers.set(evt.pointerId, { x: evt.clientX, y: evt.clientY });
			if (ui.pointers.size === 1) {
				ui.gesture = { type: 'pan', moved: false, sx: evt.clientX, sy: evt.clientY, camx: ui.cam.x, camy: ui.cam.y };
			} else if (ui.pointers.size === 2) {
				var pts = Array.from(ui.pointers.values());
				var d0 = Math.hypot(pts[0].x - pts[1].x, pts[0].y - pts[1].y);
				ui.gesture = {
					type: 'pinch',
					dist: d0,
					dist0: d0,
					zoomIndex: zoomIndex(),
					mid: { x: (pts[0].x + pts[1].x) / 2, y: (pts[0].y + pts[1].y) / 2 }
				};
			}
			render();
		});

		els.canvas.addEventListener('pointermove', function (evt) {
			if (ui.pointers.has(evt.pointerId)) ui.pointers.set(evt.pointerId, { x: evt.clientX, y: evt.clientY });
			var g = ui.gesture;
			if (g && g.type === 'pan' && ui.pointers.size === 1) {
				var dx = evt.clientX - g.sx, dy = evt.clientY - g.sy;
				if (!g.moved && Math.sqrt(dx * dx + dy * dy) > 4) g.moved = true;
				if (g.moved) {
					var sc = scale();
					ui.cam.x = g.camx - dx / sc;
					ui.cam.y = g.camy - dy / sc;
					clampCamera();
					render();
				}
				return;
			}
			if (g && g.type === 'pinch' && ui.pointers.size === 2) {
				var pts = Array.from(ui.pointers.values());
				var dist = Math.hypot(pts[0].x - pts[1].x, pts[0].y - pts[1].y);
				var mid = { x: (pts[0].x + pts[1].x) / 2, y: (pts[0].y + pts[1].y) / 2 };
				if (g.dist0 > 0) {
					var ratio = dist / g.dist0;
					var stepDir = ratio >= 1.3 ? 1 : (ratio <= 0.77 ? -1 : 0);
					if (stepDir) {
						g.zoomIndex = clamp(g.zoomIndex + stepDir, 0, ZOOM_LEVELS.length - 1);
						g.dist0 = dist;
						var rect = els.canvas.getBoundingClientRect();
						setZoomAtScreen(mid.x - rect.left, mid.y - rect.top, ZOOM_LEVELS[g.zoomIndex]);
						clampCamera();
					}
				}
				g.mid = mid;
				render();
				updateZoomLabel();
				return;
			}
			if (evt.pointerType === 'mouse') updateHover(evt);
		});

		function endPointer(evt) {
			var wasTap = ui.gesture && ui.gesture.type === 'pan' && !ui.gesture.moved && ui.pointers.size === 1;
			ui.pointers.delete(evt.pointerId);
			if (wasTap) {
				var node = nodeAtScreen(ui.gesture.sx - els.canvas.getBoundingClientRect().left, ui.gesture.sy - els.canvas.getBoundingClientRect().top);
				if (node) attemptPlace(node.x, node.y);
			}
			if (ui.pointers.size === 0) {
				ui.gesture = null;
			} else if (ui.pointers.size === 1) {
				var rem = Array.from(ui.pointers.values())[0];
				ui.gesture = { type: 'pan', moved: true, sx: rem.x, sy: rem.y, camx: ui.cam.x, camy: ui.cam.y };
			}
		}
		els.canvas.addEventListener('pointerup', endPointer);
		els.canvas.addEventListener('pointercancel', function (evt) {
			ui.pointers.delete(evt.pointerId);
			if (ui.pointers.size === 0) ui.gesture = null;
		});
		els.canvas.addEventListener('pointerleave', function (evt) {
			if (ui.pointers.size === 0 && ui.hover) { ui.hover = null; render(); }
		});

		els.canvas.addEventListener('wheel', function (evt) {
			evt.preventDefault();
			var p = localPoint(evt);
			if (evt.ctrlKey || evt.metaKey) {
				/* one discrete level per wheel notch, however small the deltas are */
				ui.wheelAccum += evt.deltaY;
				var threshold = 40;
				while (ui.wheelAccum <= -threshold) { stepZoom(1, p.x, p.y); ui.wheelAccum += threshold; }
				while (ui.wheelAccum >= threshold) { stepZoom(-1, p.x, p.y); ui.wheelAccum -= threshold; }
			} else {
				ui.wheelAccum = 0;
				var sc = scale();
				ui.cam.x += (evt.deltaX || 0) / sc;
				ui.cam.y += (evt.deltaY || 0) / sc;
				clampCamera();
			}
			render();
			updateZoomLabel();
		}, { passive: false });

		els.canvas.addEventListener('keydown', function (evt) {
			var key = evt.key;
			var c = ui.cursor;
			var handled = true;
			if (key === 'ArrowLeft') c.x -= 1;
			else if (key === 'ArrowRight') c.x += 1;
			else if (key === 'ArrowUp') c.y -= 1;
			else if (key === 'ArrowDown') c.y += 1;
			else if (key === 'Enter' || key === ' ' || key === 'Spacebar') { attemptPlace(c.x, c.y); }
			else if (key === '+' || key === '=') { stepZoom(1, viewCenterX(), ui.metrics.cssH / 2); }
			else if (key === '-' || key === '_') { stepZoom(-1, viewCenterX(), ui.metrics.cssH / 2); }
			else handled = false;
			if (!handled) return;
			evt.preventDefault();
			ui.keyboard = true;
			ensureCursorVisible();
			render();
			updateZoomLabel();
		});

		els.canvas.addEventListener('focus', render);
		els.canvas.addEventListener('blur', render);

		els.startBtn.addEventListener('click', startGame);
		els.undoBtn.addEventListener('click', undo);
		els.finishBtn.addEventListener('click', function () {
			if (ui.ended) {
				if (!els.resultDialog.open) els.resultDialog.showModal();
				return;
			}
			askConfirm({
				title: 'Завершить партию?',
				lead: 'Партия закончится, а победитель определится по числу пленных.',
				okLabel: 'Завершить',
				onOk: function () { showResult(null, 'manual'); }
			});
		});
		els.themeBtn.addEventListener('click', toggleTheme);
		els.rulesBtn.addEventListener('click', function () { els.rulesDialog.showModal(); });
		els.zoomIn.addEventListener('click', function () {
			stepZoom(1, viewCenterX(), ui.metrics.cssH / 2); render(); updateZoomLabel();
		});
		els.zoomOut.addEventListener('click', function () {
			stepZoom(-1, viewCenterX(), ui.metrics.cssH / 2); render(); updateZoomLabel();
		});
		els.centerLast.addEventListener('click', centerOnLast);

		Array.prototype.forEach.call(els.modeOpts, function (btn) {
			btn.addEventListener('click', function () {
				var next = btn.getAttribute('data-mode');
				if (next === ui.mode) return;
				ui.mode = next;
				applySettingsUI();
				saveSetting('dots:mode', next);
				newGame();
			});
		});

		Array.prototype.forEach.call(els.difficultyOpts, function (btn) {
			btn.addEventListener('click', function () {
				ui.difficulty = btn.getAttribute('data-difficulty');
				applySettingsUI();
				saveSetting('dots:difficulty', ui.difficulty);
			});
		});

		Array.prototype.forEach.call(els.firstOpts, function (btn) {
			btn.addEventListener('click', function () {
				var next = btn.getAttribute('data-first');
				if (next === ui.first) return;
				ui.first = next;
				applySettingsUI();
				saveSetting('dots:first', next);
				newGame();
			});
		});

		Array.prototype.forEach.call(els.sizeOpts, function (btn) {
			btn.addEventListener('click', function () {
				var next = btn.getAttribute('data-size');
				if (next === ui.size) return;
				ui.size = next;
				applySettingsUI();
				saveSetting('dots:size', next);
				newGame();
			});
		});

		els.timeDown.addEventListener('click', function () { stepTime(-1); });
		els.timeUp.addEventListener('click', function () { stepTime(1); });
		els.timeNone.addEventListener('click', clearTimeLimit);
		els.panelBtn.addEventListener('click', togglePanel);

		els.confirmOk.addEventListener('click', function () {
			var cb = confirmCallback;
			confirmCallback = null;
			els.confirmDialog.close();
			if (cb) cb();
		});
		els.confirmCancel.addEventListener('click', function () { confirmCallback = null; });
		els.confirmDialog.addEventListener('close', function () { confirmCallback = null; });

		Array.prototype.forEach.call(document.querySelectorAll('[data-close]'), function (btn) {
			btn.addEventListener('click', function () {
				var dlg = btn.closest('dialog');
				if (dlg) dlg.close();
				if (dlg === els.resultDialog) newGame();
			});
		});
		Array.prototype.forEach.call(document.querySelectorAll('dialog'), function (dlg) {
			dlg.addEventListener('click', function (evt) {
				if (evt.target !== dlg) return;
				dlg.close();
				if (dlg === els.resultDialog) newGame();
			});
		});
		/* Closing the result window (Esc or a close button) clears the board. */
		els.resultDialog.addEventListener('close', function () { newGame(); });

		if (window.ResizeObserver) {
			var ro = new ResizeObserver(function () { fit(); render(); });
			ro.observe(els.boardFrame);
		} else {
			window.addEventListener('resize', function () { fit(); render(); });
		}
	}

	function ensureCursorVisible() {
		var b = ui.state.bounds;
		if (b) {
			ui.cursor.x = clamp(ui.cursor.x, b.x0, b.x1);
			ui.cursor.y = clamp(ui.cursor.y, b.y0, b.y1);
		}
		var sc = scale();
		var halfW = (ui.metrics.cssW - panelInsetX()) / 2 / sc;
		var halfH = ui.metrics.cssH / 2 / sc;
		var marginX = halfW * 0.72, marginY = halfH * 0.72;
		if (ui.cursor.x < ui.cam.x - marginX) ui.cam.x = ui.cursor.x + marginX;
		if (ui.cursor.x > ui.cam.x + marginX) ui.cam.x = ui.cursor.x - marginX;
		if (ui.cursor.y < ui.cam.y - marginY) ui.cam.y = ui.cursor.y + marginY;
		if (ui.cursor.y > ui.cam.y + marginY) ui.cam.y = ui.cursor.y - marginY;
		clampCamera();
	}

	function saveSetting(k, v) { try { localStorage.setItem(k, v); } catch (err) {} }
	function loadSetting(k, f) { try { return localStorage.getItem(k) || f; } catch (err) { return f; } }

	/* ------------------------------------------------------------- startup --- */

	function init() {
		els.boardFrame = $('boardFrame');
		els.canvas = $('board');
		els.turn = $('turn');
		els.turnText = $('turnText');
		els.turnClock = $('turnClock');
		els.dotCount = $('dotCount');
		els.moveCount = $('moveCount');
		els.card1 = $('card1');
		els.card2 = $('card2');
		els.score1 = $('score1');
		els.score2 = $('score2');
		els.captured1 = $('captured1');
		els.captured2 = $('captured2');
		els.you1 = $('you1');
		els.you2 = $('you2');
		els.startBtn = $('startBtn');
		els.undoBtn = $('undoBtn');
		els.finishBtn = $('finishBtn');
		els.themeBtn = $('themeBtn');
		els.rulesBtn = $('rulesBtn');
		els.zoomIn = $('zoomIn');
		els.zoomOut = $('zoomOut');
		els.centerLast = $('centerLast');
		els.rulesDialog = $('rulesDialog');
		els.resultDialog = $('resultDialog');
		els.resultTitle = $('resultTitle');
		els.resultLead = $('resultLead');
		els.resultBadge = $('resultBadge');
		els.resultName1 = $('resultName1');
		els.resultName2 = $('resultName2');
		els.resultScore1 = $('resultScore1');
		els.resultScore2 = $('resultScore2');
		els.confirmDialog = $('confirmDialog');
		els.confirmTitle = $('confirmTitle');
		els.confirmLead = $('confirmLead');
		els.confirmOk = $('confirmOk');
		els.confirmCancel = $('confirmCancel');
		els.modeOpts = document.querySelectorAll('[data-mode]');
		els.sizeOpts = document.querySelectorAll('[data-size]');
		els.difficultyOpts = document.querySelectorAll('[data-difficulty]');
		els.firstOpts = document.querySelectorAll('[data-first]');
		els.firstSetting = $('firstSetting');
		els.timeStepper = $('timeStepper');
		els.timeValue = $('timeValue');
		els.timeDown = $('timeDown');
		els.timeUp = $('timeUp');
		els.timeNone = $('timeNone');
		els.panel = document.querySelector('.panel');
		els.panelBtn = $('panelBtn');
		els.settingsEl = document.querySelector('.settings');
		els.scoreEl = document.querySelector('.score');
		els.panelStatus = document.querySelector('.panel__status');
		els.difficultySetting = $('difficultySetting');
		els.timeLeft = $('timeLeft');
		els.timeSep = $('timeSep');
		els.live = $('live');

		initTheme();
		ui.mode = loadSetting('dots:mode', 'pvp') === 'bot' ? 'bot' : 'pvp';
		var size = loadSetting('dots:size', 'infinite');
		ui.size = FIELD_SIZES.hasOwnProperty(size) ? size : 'infinite';
		var diff = loadSetting('dots:difficulty', 'medium');
		ui.difficulty = DIFFICULTY.hasOwnProperty(diff) ? diff : 'medium';
		ui.first = loadSetting('dots:first', 'human') === 'bot' ? 'bot' : 'human';
		var storedIndex = parseInt(loadSetting('dots:timeIndex', '0'), 10);
		ui.timeIndex = isNaN(storedIndex) ? 0 : Math.max(0, storedIndex);
		ui.timeLimit = Math.max(0, parseInt(loadSetting('dots:time', '0'), 10) || 0);
		if (ui.timeLimit > 0) {
			var found = -1;
			for (var ti = 0; ti < 100000; ti++) {
				var tv = timeAt(ti);
				if (tv === ui.timeLimit) { found = ti; break; }
				if (tv > ui.timeLimit) break;
			}
			if (found >= 0) ui.timeIndex = found; else ui.timeLimit = 0;
		}
		/* The side panel always starts open on a fresh page load. */
		ui.panelHidden = false;
		applyPanelUI();
		applySettingsUI();
		newGame();
		bindEvents();
		updatePanel();
	}

	if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init);
	else init();
})();
