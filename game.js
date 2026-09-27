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
	var MIN_ZOOM = 0.5;
	var MAX_ZOOM = 1.5;

	var NAMES = { 1: 'Синие', 2: 'Красные' };
	var NAMES_DATIVE = { 1: 'синим', 2: 'красным' };

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
		cursor: { x: 0, y: 0 },
		keyboard: false,
		hover: null,
		flash: null,
		thinking: false,
		ended: false,
		palette: null,
		pointers: new Map(),
		gesture: null
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

	function worldToScreen(wx, wy) {
		var sc = scale();
		return [ui.metrics.cssW / 2 + (wx - ui.cam.x) * sc, ui.metrics.cssH / 2 + (wy - ui.cam.y) * sc];
	}

	function screenToWorld(sx, sy) {
		var sc = scale();
		return [ui.cam.x + (sx - ui.metrics.cssW / 2) / sc, ui.cam.y + (sy - ui.metrics.cssH / 2) / sc];
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
		var dx = sx - (ui.metrics.cssW / 2 + (x - ui.cam.x) * sc);
		var dy = sy - (ui.metrics.cssH / 2 + (y - ui.cam.y) * sc);
		if (Math.sqrt(dx * dx + dy * dy) > sc * 0.62) return null;
		return { x: x, y: y };
	}

	function zoomAtScreen(sx, sy, factor) {
		var before = screenToWorld(sx, sy);
		ui.cam.zoom = clamp(ui.cam.zoom * factor, MIN_ZOOM, MAX_ZOOM);
		var after = screenToWorld(sx, sy);
		ui.cam.x += before[0] - after[0];
		ui.cam.y += before[1] - after[1];
	}

	function updateZoomLabel() {
		if (els.zoomLabel) els.zoomLabel.textContent = Math.round(ui.cam.zoom * 100) + '%';
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
	 */
	function extendOutline(state, owner, touch, edges) {
		var cands = outlineCandidates(state, owner, touch);
		if (!cands.length) return;

		var used = new Set();
		var deg = new Map();
		function bump(k) { deg.set(k, (deg.get(k) || 0) + 1); }
		for (var i = 0; i < edges.length; i++) {
			if (edges[i].owner !== owner) continue;
			var ea = E.key(edges[i].ax, edges[i].ay);
			var eb = E.key(edges[i].bx, edges[i].by);
			var ek0 = edgeKey(ea, eb);
			if (used.has(ek0)) continue;
			used.add(ek0); bump(ea); bump(eb);
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

		for (var u = 0; u < order.length; u++) {
			var from = order[u];
			if ((deg.get(from) || 0) >= limit(from)) continue;
			var nb = neighbors.get(from).slice().sort(function (a, b) {
				if (a.ortho !== b.ortho) return a.ortho ? -1 : 1;
				return (deg.get(a.k) || 0) - (deg.get(b.k) || 0);
			});
			for (var j = 0; j < nb.length && (deg.get(from) || 0) < limit(from); j++) {
				var to = nb[j].k;
				if ((deg.get(to) || 0) >= limit(to)) continue;
				var ek2 = edgeKey(from, to);
				if (used.has(ek2)) continue;
				used.add(ek2); bump(from); bump(to);
				var p1 = E.parseKey(from), p2 = E.parseKey(to);
				edges.push({ ax: p1[0], ay: p1[1], bx: p2[0], by: p2[1], owner: owner });
			}
		}
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
		var halfW = m.cssW / 2, halfH = m.cssH / 2;

		ctx.setTransform(m.dpr, 0, 0, m.dpr, 0, 0);
		ctx.clearRect(0, 0, m.cssW, m.cssH);
		ctx.fillStyle = pal.boardPaper;
		ctx.fillRect(0, 0, m.cssW, m.cssH);

		function sx(wx) { return halfW + (wx - ui.cam.x) * sc; }
		function sy(wy) { return halfH + (wy - ui.cam.y) * sc; }
		var left = ui.cam.x - halfW / sc, right = ui.cam.x + halfW / sc;
		var top = ui.cam.y - halfH / sc, bottom = ui.cam.y + halfH / sc;

		/* grid, with an adaptive step so lines never crowd together */
		var step = 1;
		while (sc * step < 14) step *= 2;
		ctx.lineWidth = 1;
		ctx.strokeStyle = pal.grid;
		var gx0 = Math.floor(left / step) * step;
		for (var gx = gx0; gx <= right; gx += step) {
			var X = Math.round(sx(gx)) + 0.5;
			ctx.beginPath(); ctx.moveTo(X, 0); ctx.lineTo(X, m.cssH); ctx.stroke();
		}
		var gy0 = Math.floor(top / step) * step;
		for (var gy = gy0; gy <= bottom; gy += step) {
			var Y = Math.round(sy(gy)) + 0.5;
			ctx.beginPath(); ctx.moveTo(0, Y); ctx.lineTo(m.cssW, Y); ctx.stroke();
		}
		/* fortress outlines */
		ctx.lineCap = 'round';
		ctx.lineJoin = 'round';
		ctx.lineWidth = Math.max(1.5, sc * 0.11);
		for (var i = 0; i < ui.scene.edges.length; i++) {
			var e = ui.scene.edges[i];
			ctx.strokeStyle = e.owner === 1 ? pal.p1 : pal.p2;
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
				/* a prisoner looks like an ordinary dot, just half transparent */
				var own = E.ownerOf(v);
				ctx.fillStyle = own === 1 ? pal.p1 : pal.p2;
				ctx.globalAlpha = 0.5;
			}
			ctx.beginPath(); ctx.arc(px, py, sc * 0.15, 0, TAU); ctx.fill();
			ctx.globalAlpha = 1;
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
		return ui.ended || (ui.mode === 'bot' && (ui.state.turn === 2 || ui.thinking));
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
		ui.hover = null;
		ui.cursor.x = x; ui.cursor.y = y;
		extendScene(res.player, res.claimed);
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

	/* ----------------------------------------------------------- new game --- */

	function newGame() {
		ui.state = E.createGame({ extraTurn: false });
		ui.history = [];
		ui.ended = false;
		ui.thinking = false;
		ui.hover = null;
		ui.flash = null;
		ui.keyboard = false;
		ui.cursor.x = 0; ui.cursor.y = 0;
		ui.cam.x = 0; ui.cam.y = 0; ui.cam.zoom = 1;
		ui.scene = { edges: [] };
		updateZoomLabel();
		fit();
		render();
		updatePanel();
	}

	/* --------------------------------------------------------------- panel --- */

	function updatePanel() {
		var s = ui.state;
		els.score1.textContent = s.score[1];
		els.score2.textContent = s.score[2];
		els.captured1.textContent = E.activeCount(s, 1);
		els.captured2.textContent = E.activeCount(s, 2);
		els.dotCount.textContent = 'Точек: ' + (E.activeCount(s, 1) + E.activeCount(s, 2));
		els.moveCount.textContent = 'Ходов: ' + s.moveCount;

		var active = ui.ended ? 0 : s.turn;
		els.card1.classList.toggle('is-active', active === 1);
		els.card2.classList.toggle('is-active', active === 2);

		els.turn.setAttribute('data-player', String(s.turn));
		if (ui.ended) {
			els.turn.classList.remove('is-thinking');
			els.turnText.textContent = 'Партия завершена';
		} else if (ui.thinking) {
			els.turn.classList.add('is-thinking');
			els.turnText.textContent = NAMES[s.turn] + ' думают';
		} else {
			els.turn.classList.remove('is-thinking');
			els.turnText.textContent = 'Ход: ' + NAMES[s.turn];
		}

		var bot = ui.mode === 'bot';
		els.you1.hidden = !bot;
		els.you2.hidden = !bot;
		els.you2.textContent = 'соперник';

		els.undoBtn.disabled = !ui.history.length || ui.thinking;
		els.finishBtn.disabled = ui.ended || s.moveCount === 0 || ui.thinking;
		els.resignBtn.disabled = ui.ended || s.moveCount === 0 || ui.thinking;
		els.canvas.classList.toggle('is-locked', isLocked());
		updateZoomLabel();
	}

	/* ----------------------------------------------------------------- bot --- */

	function scheduleBot() {
		if (ui.mode !== 'bot' || ui.ended || ui.thinking) return;
		ui.thinking = true;
		updatePanel();
		window.setTimeout(function () {
			ui.thinking = false;
			if (ui.mode !== 'bot' || ui.ended || ui.state.turn !== 2) { render(); updatePanel(); return; }
			var move = E.bestMove(ui.state, 2, { timeBudget: 900, maxDepth: 6, maxMoves: 12 });
			if (!move) { render(); updatePanel(); return; }
			commitMove(move.x, move.y);
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
		if (ui.thinking || !ui.history.length) return;
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
		var tx = target ? target.x : 0;
		var ty = target ? target.y : 0;
		animateCam(tx, ty, 320);
	}

	function animateCam(tx, ty, duration) {
		var reduced = window.matchMedia && window.matchMedia('(prefers-reduced-motion: reduce)').matches;
		if (reduced) { ui.cam.x = tx; ui.cam.y = ty; render(); return; }
		var startX = ui.cam.x, startY = ui.cam.y, t0 = performance.now();
		function frame(now) {
			var t = Math.min(1, (now - t0) / duration);
			var e = 1 - Math.pow(1 - t, 3);
			ui.cam.x = startX + (tx - startX) * e;
			ui.cam.y = startY + (ty - startY) * e;
			render();
			if (t < 1) requestAnimationFrame(frame);
		}
		requestAnimationFrame(frame);
	}

	function applySettingsUI() {
		Array.prototype.forEach.call(els.segmented, function (btn) {
			var on = btn.getAttribute('data-mode') === ui.mode;
			btn.classList.toggle('is-active', on);
			btn.setAttribute('aria-pressed', on ? 'true' : 'false');
		});
	}

	/* -------------------------------------------------------------- dialogs --- */

	function showResult(winner, reason) {
		ui.ended = true;
		ui.thinking = false;
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
				ui.gesture = {
					type: 'pinch',
					dist: Math.hypot(pts[0].x - pts[1].x, pts[0].y - pts[1].y),
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
					render();
				}
				return;
			}
			if (g && g.type === 'pinch' && ui.pointers.size === 2) {
				var pts = Array.from(ui.pointers.values());
				var dist = Math.hypot(pts[0].x - pts[1].x, pts[0].y - pts[1].y);
				var mid = { x: (pts[0].x + pts[1].x) / 2, y: (pts[0].y + pts[1].y) / 2 };
				if (g.dist > 0) {
					var rect = els.canvas.getBoundingClientRect();
					zoomAtScreen(mid.x - rect.left, mid.y - rect.top, dist / g.dist);
				}
				g.dist = dist;
				g.mid = mid;
				render();
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
				zoomAtScreen(p.x, p.y, Math.exp(-evt.deltaY * 0.002));
			} else {
				var sc = scale();
				ui.cam.x += (evt.deltaX || 0) / sc;
				ui.cam.y += (evt.deltaY || 0) / sc;
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
			else if (key === '+' || key === '=') { zoomAtScreen(ui.metrics.cssW / 2, ui.metrics.cssH / 2, 1.25); }
			else if (key === '-' || key === '_') { zoomAtScreen(ui.metrics.cssW / 2, ui.metrics.cssH / 2, 0.8); }
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

		els.newBtn.addEventListener('click', requestNewGame);
		els.undoBtn.addEventListener('click', undo);
		els.finishBtn.addEventListener('click', function () {
			if (ui.ended || ui.state.moveCount === 0) return;
			showResult(null, 'manual');
		});
		els.resignBtn.addEventListener('click', requestResign);
		els.themeBtn.addEventListener('click', toggleTheme);
		els.rulesBtn.addEventListener('click', function () { els.rulesDialog.showModal(); });
		els.zoomIn.addEventListener('click', function () {
			zoomAtScreen(ui.metrics.cssW / 2, ui.metrics.cssH / 2, 1.25); render(); updateZoomLabel();
		});
		els.zoomOut.addEventListener('click', function () {
			zoomAtScreen(ui.metrics.cssW / 2, ui.metrics.cssH / 2, 0.8); render(); updateZoomLabel();
		});
		els.zoomReset.addEventListener('click', function () {
			zoomAtScreen(ui.metrics.cssW / 2, ui.metrics.cssH / 2, 1 / ui.cam.zoom); render(); updateZoomLabel();
		});
		els.centerLast.addEventListener('click', centerOnLast);

		Array.prototype.forEach.call(els.segmented, function (btn) {
			btn.addEventListener('click', function () {
				var next = btn.getAttribute('data-mode');
				if (next === ui.mode) return;
				ui.mode = next;
				applySettingsUI();
				saveSetting('dots:mode', next);
				newGame();
			});
		});

		els.confirmOk.addEventListener('click', function () {
			var cb = confirmCallback;
			confirmCallback = null;
			els.confirmDialog.close();
			if (cb) cb();
		});
		els.confirmCancel.addEventListener('click', function () { confirmCallback = null; });
		els.confirmDialog.addEventListener('close', function () { confirmCallback = null; });
		els.resultNew.addEventListener('click', function () { els.resultDialog.close(); newGame(); });

		Array.prototype.forEach.call(document.querySelectorAll('[data-close]'), function (btn) {
			btn.addEventListener('click', function () {
				var dlg = btn.closest('dialog');
				if (dlg) dlg.close();
			});
		});
		Array.prototype.forEach.call(document.querySelectorAll('dialog'), function (dlg) {
			dlg.addEventListener('click', function (evt) { if (evt.target === dlg) dlg.close(); });
		});

		if (window.ResizeObserver) {
			var ro = new ResizeObserver(function () { fit(); render(); });
			ro.observe(els.boardFrame);
		} else {
			window.addEventListener('resize', function () { fit(); render(); });
		}
	}

	function ensureCursorVisible() {
		var sc = scale();
		var halfW = ui.metrics.cssW / 2 / sc;
		var halfH = ui.metrics.cssH / 2 / sc;
		var marginX = halfW * 0.72, marginY = halfH * 0.72;
		if (ui.cursor.x < ui.cam.x - marginX) ui.cam.x = ui.cursor.x + marginX;
		if (ui.cursor.x > ui.cam.x + marginX) ui.cam.x = ui.cursor.x - marginX;
		if (ui.cursor.y < ui.cam.y - marginY) ui.cam.y = ui.cursor.y + marginY;
		if (ui.cursor.y > ui.cam.y + marginY) ui.cam.y = ui.cursor.y - marginY;
	}

	function saveSetting(k, v) { try { localStorage.setItem(k, v); } catch (err) {} }
	function loadSetting(k, f) { try { return localStorage.getItem(k) || f; } catch (err) { return f; } }

	function requestNewGame() {
		if (ui.state.moveCount === 0) { newGame(); return; }
		askConfirm({ title: 'Начать заново?', lead: 'Текущая партия будет сброшена.', okLabel: 'Начать заново', onOk: newGame });
	}

	function requestResign() {
		if (ui.ended || ui.state.moveCount === 0) return;
		var resigner = ui.state.turn;
		var winner = resigner === 1 ? 2 : 1;
		askConfirm({
			title: 'Сдаться?',
			lead: NAMES[resigner] + ' признают поражение, победа достанется ' + NAMES_DATIVE[winner] + '.',
			okLabel: 'Сдаться',
			danger: true,
			onOk: function () { showResult(winner, 'resign'); }
		});
	}

	/* ------------------------------------------------------------- startup --- */

	function init() {
		els.boardFrame = $('boardFrame');
		els.canvas = $('board');
		els.turn = $('turn');
		els.turnText = $('turnText');
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
		els.undoBtn = $('undoBtn');
		els.newBtn = $('newBtn');
		els.finishBtn = $('finishBtn');
		els.resignBtn = $('resignBtn');
		els.themeBtn = $('themeBtn');
		els.rulesBtn = $('rulesBtn');
		els.zoomIn = $('zoomIn');
		els.zoomOut = $('zoomOut');
		els.zoomReset = $('zoomReset');
		els.zoomLabel = $('zoomLabel');
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
		els.resultNew = $('resultNew');
		els.confirmDialog = $('confirmDialog');
		els.confirmTitle = $('confirmTitle');
		els.confirmLead = $('confirmLead');
		els.confirmOk = $('confirmOk');
		els.confirmCancel = $('confirmCancel');
		els.segmented = document.querySelectorAll('.segmented__opt');
		els.live = $('live');

		initTheme();
		ui.mode = loadSetting('dots:mode', 'pvp') === 'bot' ? 'bot' : 'pvp';
		applySettingsUI();
		newGame();
		bindEvents();
		updatePanel();
	}

	if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init);
	else init();
})();
