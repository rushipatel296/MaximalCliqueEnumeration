(() => {
  'use strict';

  const ALGOS = [
    { id: 'els', name: 'ELS', color: '--series-1' },
    { id: 'tomita', name: 'Tomita', color: '--series-2' },
    { id: 'chiba', name: 'Chiba', color: '--series-3' },
  ];
  const CHIBA_CALL_LIMIT = 4e6;

  const $ = (id) => document.getElementById(id);
  const css = (name) => getComputedStyle(document.documentElement).getPropertyValue(name).trim();
  const fmtInt = (x) => x.toLocaleString('en-US');

  // ---------- algorithms (ports of the C++ in /src) ----------

  // Bron-Kerbosch with Tomita pivot: pivot u in P ∪ X maximising |P ∩ N(u)|.
  function bkPivot(adj, R, P, X, out, ctr) {
    ctr.calls++;
    if (P.size === 0) {
      if (X.size === 0) out.push(R.slice());
      return;
    }
    let pivot = -1, best = -1;
    for (const S of [P, X]) {
      for (const u of S) {
        let c = 0;
        for (const w of P) if (adj[u].has(w)) c++;
        if (c > best) { best = c; pivot = u; }
      }
    }
    for (const v of [...P]) {
      if (adj[pivot].has(v)) continue;
      const Nv = adj[v];
      const P2 = new Set(), X2 = new Set();
      for (const w of P) if (Nv.has(w)) P2.add(w);
      for (const w of X) if (Nv.has(w)) X2.add(w);
      R.push(v);
      bkPivot(adj, R, P2, X2, out, ctr);
      R.pop();
      P.delete(v);
      X.add(v);
    }
  }

  function degeneracyOrder(adj) {
    const n = adj.length;
    const deg = adj.map((s) => s.size);
    const done = new Array(n).fill(false);
    const order = [];
    for (let k = 0; k < n; k++) {
      let v = -1;
      for (let u = 0; u < n; u++) if (!done[u] && (v < 0 || deg[u] < deg[v])) v = u;
      done[v] = true;
      order.push(v);
      for (const w of adj[v]) if (!done[w]) deg[w]--;
    }
    return order;
  }

  function runEls(adj) {
    const out = [], ctr = { calls: 0 };
    const order = degeneracyOrder(adj);
    const rank = new Array(adj.length);
    order.forEach((v, i) => { rank[v] = i; });
    for (const v of order) {
      const P = new Set(), X = new Set();
      for (const w of adj[v]) (rank[w] > rank[v] ? P : X).add(w);
      bkPivot(adj, [v], P, X, out, ctr);
    }
    return { cliques: out, calls: ctr.calls };
  }

  function runTomita(adj) {
    const out = [], ctr = { calls: 0 };
    for (let v = 0; v < adj.length; v++) {
      const P = new Set(), X = new Set();
      for (const w of adj[v]) (w > v ? P : X).add(w);
      bkPivot(adj, [v], P, X, out, ctr);
    }
    return { cliques: out, calls: ctr.calls };
  }

  // Include/exclude each vertex in degree order, keep cliques that are maximal at the leaves.
  function runChiba(adj) {
    const n = adj.length;
    const order = [...adj.keys()].sort((a, b) => adj[b].size - adj[a].size || a - b);
    const out = [], C = [];
    let calls = 0, aborted = false;
    const isMaximal = () => {
      for (let v = 0; v < n; v++) {
        if (C.includes(v)) continue;
        if (C.every((u) => adj[u].has(v))) return false;
      }
      return true;
    };
    const update = (i) => {
      if (aborted) return;
      if (++calls > CHIBA_CALL_LIMIT) { aborted = true; return; }
      if (i === n) {
        if (C.length && isMaximal()) out.push(C.slice());
        return;
      }
      const v = order[i];
      if (C.every((u) => adj[u].has(v))) {
        C.push(v);
        update(i + 1);
        C.pop();
      }
      update(i + 1);
    };
    update(0);
    return { cliques: out, calls, aborted };
  }

  const RUNNERS = { els: runEls, tomita: runTomita, chiba: runChiba };

  // ---------- graph state ----------

  const state = { n: 0, adj: [], pos: [], cliques: [], selected: 0, picked: -1 };

  function randomGraph(n, p) {
    const adj = Array.from({ length: n }, () => new Set());
    for (let u = 0; u < n; u++)
      for (let v = u + 1; v < n; v++)
        if (Math.random() < p) { adj[u].add(v); adj[v].add(u); }
    return adj;
  }

  function layout(adj) {
    const n = adj.length;
    const pos = Array.from({ length: n }, (_, i) => {
      const a = (2 * Math.PI * i) / n;
      return { x: 0.5 + 0.35 * Math.cos(a) + (Math.random() - 0.5) * 0.05, y: 0.5 + 0.35 * Math.sin(a) + (Math.random() - 0.5) * 0.05 };
    });
    const k = 0.9 / Math.sqrt(Math.max(n, 1));
    let t = 0.08;
    for (let it = 0; it < 350; it++) {
      const disp = pos.map(() => ({ x: 0, y: 0 }));
      for (let i = 0; i < n; i++) {
        for (let j = i + 1; j < n; j++) {
          let dx = pos[i].x - pos[j].x, dy = pos[i].y - pos[j].y;
          const d = Math.max(Math.hypot(dx, dy), 1e-4);
          let f = (k * k) / d;
          if (adj[i].has(j)) f -= (d * d) / k;
          dx = (dx / d) * f; dy = (dy / d) * f;
          disp[i].x += dx; disp[i].y += dy;
          disp[j].x -= dx; disp[j].y -= dy;
        }
        disp[i].x += (0.5 - pos[i].x) * 0.05;
        disp[i].y += (0.5 - pos[i].y) * 0.05;
      }
      for (let i = 0; i < n; i++) {
        const d = Math.hypot(disp[i].x, disp[i].y) || 1;
        const s = Math.min(d, t) / d;
        pos[i].x = Math.min(0.97, Math.max(0.03, pos[i].x + disp[i].x * s));
        pos[i].y = Math.min(0.97, Math.max(0.03, pos[i].y + disp[i].y * s));
      }
      t *= 0.985;
    }
    // normalise into the unit box
    const xs = pos.map((p) => p.x), ys = pos.map((p) => p.y);
    const minX = Math.min(...xs), maxX = Math.max(...xs), minY = Math.min(...ys), maxY = Math.max(...ys);
    const sx = maxX - minX || 1, sy = maxY - minY || 1;
    return pos.map((p) => ({ x: (p.x - minX) / sx, y: (p.y - minY) / sy }));
  }

  // ---------- compute + render panel ----------

  const canonical = (cl) => cl.map((c) => c.slice().sort((a, b) => a - b)).sort((a, b) => b.length - a.length || a.join() .localeCompare(b.join(), undefined, { numeric: true }));
  const keyOf = (list) => list.map((c) => c.join(',')).join('|');

  function recompute() {
    const results = ALGOS.map((a) => {
      const t0 = performance.now();
      const r = RUNNERS[a.id](state.adj);
      r.ms = performance.now() - t0;
      r.sorted = canonical(r.cliques);
      return { ...a, ...r };
    });
    state.cliques = results[0].sorted;
    state.selected = state.cliques.length ? 0 : -1;

    const ref = keyOf(results[0].sorted);
    $('compareBody').innerHTML = results.map((r) => {
      const ok = r.aborted || keyOf(r.sorted) === ref;
      const largest = r.sorted.length ? r.sorted[0].length : 0;
      const time = r.ms < 1 ? '<1 ms' : `${r.ms.toFixed(r.ms < 10 ? 1 : 0)} ms`;
      return `<tr><td><span class="dot" style="background:var(${r.color})"></span>${r.name}${ok ? '' : ' ⚠'}</td>
        <td>${r.aborted ? '–' : fmtInt(r.sorted.length)}</td><td>${r.aborted ? '–' : largest}</td>
        <td>${r.aborted ? '&gt; ' + fmtInt(CHIBA_CALL_LIMIT) : fmtInt(r.calls)}</td><td>${r.aborted ? 'stopped' : time}</td></tr>`;
    }).join('');

    renderCliqueList();
    renderMiniHist();
    draw();
  }

  function renderCliqueList() {
    const list = state.cliques;
    $('cliqueCount').textContent = `(${list.length})`;
    const shown = list.slice(0, 300);
    $('cliqueList').innerHTML = shown.map((c, i) =>
      `<button class="chip" role="option" data-i="${i}" aria-selected="${i === state.selected}">{${c.join(', ')}}</button>`
    ).join('') + (list.length > shown.length ? `<span class="muted">+${list.length - shown.length} more</span>` : '');
    const c = list[state.selected];
    $('hint').textContent = c
      ? `Highlighted: {${c.join(', ')}}, a maximal clique of size ${c.length}.`
      : 'No edges yet. Click two nodes to connect them.';
  }

  function renderMiniHist() {
    const counts = {};
    for (const c of state.cliques) counts[c.length] = (counts[c.length] || 0) + 1;
    const sizes = Object.keys(counts).map(Number);
    if (!sizes.length) { $('miniHist').innerHTML = ''; return; }
    const max = Math.max(...Object.values(counts));
    let html = '';
    for (let s = Math.min(...sizes); s <= Math.max(...sizes); s++) {
      const v = counts[s] || 0;
      html += `<div class="col" data-tip="${fmtInt(v)} maximal clique${v === 1 ? '' : 's'} of size ${s}">
        <span class="val">${v || ''}</span><div class="bar" style="height:${v ? Math.max(3, (v / max) * 62) : 0}px"></div><span class="lab">${s}</span></div>`;
    }
    $('miniHist').innerHTML = html;
  }

  // ---------- canvas ----------

  const canvas = $('graph');
  const ctx = canvas.getContext('2d');
  let colors = {};
  const readColors = () => {
    colors = { edge: css('--edge'), node: css('--node'), stroke: css('--node-stroke'), text: css('--text'),
      hl: css('--series-1'), hlEdge: css('--hl-edge'), pick: css('--pick'), bg: css('--surface-2') };
  };

  const PAD = 26;
  const R_NODE = () => (state.n > 26 ? 11 : 13);
  function toPx(p) {
    const w = canvas.clientWidth, h = canvas.clientHeight;
    return { x: PAD + p.x * (w - 2 * PAD), y: PAD + p.y * (h - 2 * PAD) };
  }
  function fromPx(x, y) {
    const w = canvas.clientWidth, h = canvas.clientHeight;
    return { x: Math.min(1, Math.max(0, (x - PAD) / (w - 2 * PAD))), y: Math.min(1, Math.max(0, (y - PAD) / (h - 2 * PAD))) };
  }

  function draw() {
    const dpr = window.devicePixelRatio || 1;
    const w = canvas.clientWidth, h = canvas.clientHeight;
    if (canvas.width !== Math.round(w * dpr) || canvas.height !== Math.round(h * dpr)) {
      canvas.width = Math.round(w * dpr); canvas.height = Math.round(h * dpr);
    }
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, w, h);
    const inClique = new Set(state.cliques[state.selected] || []);
    const P = state.pos.map(toPx);

    ctx.lineCap = 'round';
    for (let u = 0; u < state.n; u++) {
      for (const v of state.adj[u]) {
        if (v < u) continue;
        const hl = inClique.has(u) && inClique.has(v);
        if (hl) continue;
        ctx.strokeStyle = colors.edge; ctx.lineWidth = 1.5;
        ctx.beginPath(); ctx.moveTo(P[u].x, P[u].y); ctx.lineTo(P[v].x, P[v].y); ctx.stroke();
      }
    }
    for (const u of inClique) for (const v of inClique) {
      if (v <= u) continue;
      ctx.strokeStyle = colors.hlEdge; ctx.lineWidth = 3;
      ctx.beginPath(); ctx.moveTo(P[u].x, P[u].y); ctx.lineTo(P[v].x, P[v].y); ctx.stroke();
    }

    const r = R_NODE();
    ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    ctx.font = `600 ${r > 11 ? 12 : 11}px Inter, system-ui, sans-serif`;
    for (let u = 0; u < state.n; u++) {
      const hl = inClique.has(u);
      ctx.beginPath(); ctx.arc(P[u].x, P[u].y, r, 0, 2 * Math.PI);
      ctx.fillStyle = hl ? colors.hl : colors.node; ctx.fill();
      ctx.lineWidth = 2; ctx.strokeStyle = hl ? colors.bg : colors.stroke; ctx.stroke();
      if (u === state.picked) {
        ctx.beginPath(); ctx.arc(P[u].x, P[u].y, r + 5, 0, 2 * Math.PI);
        ctx.lineWidth = 2.5; ctx.strokeStyle = colors.pick; ctx.stroke();
      }
      ctx.fillStyle = hl ? '#ffffff' : colors.text;
      ctx.fillText(String(u), P[u].x, P[u].y + 0.5);
    }
  }

  function nodeAt(x, y) {
    const r = R_NODE() + 6;
    let best = -1, bd = Infinity;
    state.pos.forEach((p, i) => {
      const q = toPx(p);
      const d = Math.hypot(q.x - x, q.y - y);
      if (d < r && d < bd) { bd = d; best = i; }
    });
    return best;
  }

  let drag = null;
  canvas.addEventListener('pointerdown', (e) => {
    const rect = canvas.getBoundingClientRect();
    const x = e.clientX - rect.left, y = e.clientY - rect.top;
    const i = nodeAt(x, y);
    if (i < 0) { state.picked = -1; draw(); return; }
    drag = { i, x0: x, y0: y, moved: false };
    canvas.setPointerCapture(e.pointerId);
  });
  canvas.addEventListener('pointermove', (e) => {
    if (!drag) return;
    const rect = canvas.getBoundingClientRect();
    const x = e.clientX - rect.left, y = e.clientY - rect.top;
    if (!drag.moved && Math.hypot(x - drag.x0, y - drag.y0) > 4) { drag.moved = true; canvas.classList.add('dragging'); }
    if (drag.moved) { state.pos[drag.i] = fromPx(x, y); draw(); }
  });
  canvas.addEventListener('pointerup', () => {
    if (!drag) return;
    const { i, moved } = drag;
    drag = null;
    canvas.classList.remove('dragging');
    if (moved) return;
    if (state.picked < 0) { state.picked = i; draw(); return; }
    if (state.picked === i) { state.picked = -1; draw(); return; }
    const u = state.picked;
    if (state.adj[u].has(i)) { state.adj[u].delete(i); state.adj[i].delete(u); }
    else { state.adj[u].add(i); state.adj[i].add(u); }
    state.picked = -1;
    recompute();
  });

  $('cliqueList').addEventListener('click', (e) => {
    const b = e.target.closest('.chip');
    if (!b) return;
    state.selected = Number(b.dataset.i);
    for (const c of $('cliqueList').querySelectorAll('.chip')) c.setAttribute('aria-selected', c === b);
    renderCliqueListHintOnly();
    draw();
  });
  function renderCliqueListHintOnly() {
    const c = state.cliques[state.selected];
    $('hint').textContent = `Highlighted: {${c.join(', ')}}, a maximal clique of size ${c.length}.`;
  }

  function newGraph() {
    state.n = Number($('nIn').value);
    state.adj = randomGraph(state.n, Number($('pIn').value));
    state.pos = layout(state.adj);
    state.picked = -1;
    recompute();
  }
  $('nIn').addEventListener('input', (e) => { $('nOut').textContent = e.target.value; });
  $('pIn').addEventListener('input', (e) => { $('pOut').textContent = Number(e.target.value).toFixed(2); });
  $('nIn').addEventListener('change', newGraph);
  $('pIn').addEventListener('change', newGraph);
  $('regen').addEventListener('click', newGraph);
  $('clear').addEventListener('click', () => {
    state.adj = Array.from({ length: state.n }, () => new Set());
    state.pos = layout(state.adj);
    state.picked = -1;
    recompute();
  });

  // ---------- tooltip ----------

  const tip = $('tip');
  document.addEventListener('pointermove', (e) => {
    const t = e.target.closest && e.target.closest('[data-tip]');
    if (!t) { tip.hidden = true; return; }
    tip.textContent = t.dataset.tip;
    tip.hidden = false;
    const x = Math.min(e.clientX + 12, window.innerWidth - tip.offsetWidth - 8);
    tip.style.left = `${x}px`;
    tip.style.top = `${e.clientY + 14}px`;
  });

  // ---------- benchmark section ----------

  const D = window.RESULTS;
  const fmtTime = (s) => {
    if (s < 60) return `${s < 10 ? s.toFixed(2) : s.toFixed(1)} s`;
    if (s < 3600) return `${(s / 60).toFixed(1)} min`;
    return `${(s / 3600).toFixed(1)} h`;
  };
  const fmtCompact = (x) => (x >= 1e6 ? +(x / 1e6).toFixed(1) + 'M' : x >= 1e3 ? +(x / 1e3).toFixed(1) + 'K' : String(x));

  $('datasetStats').innerHTML = D.datasets.map((d) => `
    <div class="stat"><div class="name">${d.name}</div><div class="what">${d.what}</div>
      <dl><dt>Nodes</dt><dd>${fmtInt(d.nodes)}</dd><dt>Edges</dt><dd>${fmtInt(d.edges)}</dd>
      <dt>Maximal cliques</dt><dd>${fmtInt(d.cliques)}</dd><dt>Largest clique</dt><dd>${d.largest}</dd></dl></div>`).join('');

  $('timeLegend').innerHTML = ALGOS.map((a) => `<span><span class="dot" style="background:var(${a.color})"></span>${a.name}</span>`).join('');

  function timeChart() {
    const W = 760, rowH = 22, groupGap = 14, left = 96, right = 92, top = 8;
    const ticks = [1, 10, 60, 600, 3600, 36000, 86400];
    const tickLab = ['1 s', '10 s', '1 min', '10 min', '1 h', '10 h', '1 day'];
    const lo = Math.log10(0.8), hi = Math.log10(100000);
    const X = (s) => left + ((Math.log10(s) - lo) / (hi - lo)) * (W - left - right);
    const H = top + D.datasets.length * (ALGOS.length * rowH + groupGap) + 22;
    let s = `<svg viewBox="0 0 ${W} ${H}" role="img" aria-label="Sequential running time per algorithm and dataset, log scale">`;
    ticks.forEach((t, i) => {
      s += `<line class="gridline" x1="${X(t)}" x2="${X(t)}" y1="${top}" y2="${H - 20}"/>`;
      s += `<text x="${X(t)}" y="${H - 6}" text-anchor="middle">${tickLab[i]}</text>`;
    });
    let y = top;
    D.datasets.forEach((d) => {
      s += `<text class="rowlabel" x="0" y="${y + (ALGOS.length * rowH) / 2 + 4}">${d.name}</text>`;
      ALGOS.forEach((a) => {
        const [seq, par] = D.times[a.id][d.id];
        const lb = D.lowerBound[a.id] && D.lowerBound[a.id][d.id];
        const cy = y + rowH / 2;
        const x = X(seq);
        const label = lb ? `> ${fmtTime(seq)}, stopped` : fmtTime(seq);
        const tipText = `${a.name} on ${d.name}: ${lb ? 'stopped after ' + fmtTime(seq) : fmtTime(seq)}${par ? `, ${fmtTime(par)} with OpenMP` : ''}`;
        s += `<g data-tip="${tipText}">`;
        s += `<rect x="${left - 4}" y="${y}" width="${W - left}" height="${rowH}" fill="transparent"/>`;
        s += `<line x1="${X(0.8)}" x2="${x}" y1="${cy}" y2="${cy}" stroke="var(${a.color})" stroke-width="2" stroke-linecap="round" ${lb ? 'stroke-dasharray="3 4"' : ''}/>`;
        s += lb
          ? `<circle cx="${x}" cy="${cy}" r="5" fill="var(--surface)" stroke="var(${a.color})" stroke-width="2"/>`
          : `<circle cx="${x}" cy="${cy}" r="5" fill="var(${a.color})" stroke="var(--surface)" stroke-width="2"/>`;
        s += `<text x="${x + 10}" y="${cy + 4}" style="fill:var(--text)">${label}</text></g>`;
        y += rowH;
      });
      y += groupGap;
    });
    $('timeChart').innerHTML = s + '</svg>';

    let t = '<thead><tr><th>Algorithm</th>' + D.datasets.map((d) => `<th>${d.name}</th><th>${d.name} (OpenMP)</th>`).join('') + '</tr></thead><tbody>';
    ALGOS.forEach((a) => {
      t += `<tr><td>${a.name}</td>` + D.datasets.map((d) => {
        const [seq, par] = D.times[a.id][d.id];
        const lb = D.lowerBound[a.id] && D.lowerBound[a.id][d.id];
        return `<td>${lb ? '&gt; ' : ''}${fmtTime(seq)}</td><td>${par ? fmtTime(par) : '–'}</td>`;
      }).join('') + '</tr>';
    });
    $('timeTable').innerHTML = t + '</tbody>';
  }

  function distChart(id) {
    const d = D.datasets.find((x) => x.id === id);
    const entries = Object.entries(d.dist).map(([k, v]) => [Number(k), v]).sort((a, b) => a[0] - b[0]);
    const W = 760, H = 260, left = 48, right = 8, top = 22, bottom = 26;
    const maxV = Math.max(...entries.map((e) => e[1]));
    const mag = Math.pow(10, Math.floor(Math.log10(maxV / 4)));
    const tick = [1, 2, 2.5, 5, 10].map((m) => m * mag).find((t) => t * 4 >= maxV);
    const niceMax = tick * 4;
    const n = entries.length;
    const bw = (W - left - right) / n;
    const Y = (v) => top + (1 - v / niceMax) * (H - top - bottom);
    let s = `<svg viewBox="0 0 ${W} ${H}" role="img" aria-label="Maximal clique size distribution for ${d.name}">`;
    for (let k = 0; k <= 4; k++) {
      const v = (niceMax / 4) * k;
      s += `<line class="gridline" x1="${left}" x2="${W - right}" y1="${Y(v)}" y2="${Y(v)}"/>`;
      s += `<text x="${left - 6}" y="${Y(v) + 4}" text-anchor="end">${fmtCompact(v)}</text>`;
    }
    const labelEvery = n > 30 ? 5 : n > 16 ? 2 : 1;
    const peak = entries.reduce((a, b) => (b[1] > a[1] ? b : a));
    entries.forEach(([size, v], i) => {
      const x = left + i * bw;
      const gap = Math.min(2, bw * 0.2);
      const w = bw - gap;
      const h = Math.max(1, H - bottom - Y(v));
      const rad = Math.min(4, w / 2, h);
      const y0 = H - bottom;
      s += `<g data-tip="Size ${size}: ${fmtInt(v)} maximal cliques">`;
      s += `<rect x="${x}" y="${top}" width="${bw}" height="${H - top - bottom}" fill="transparent"/>`;
      s += `<path d="M${x + gap / 2},${y0} V${y0 - h + rad} q0,-${rad} ${rad},-${rad} H${x + gap / 2 + w - rad} q${rad},0 ${rad},${rad} V${y0} Z" fill="var(--seq)"/>`;
      s += '</g>';
      if (size % labelEvery === 0 || n <= 16) s += `<text x="${x + bw / 2}" y="${H - 8}" text-anchor="middle">${size}</text>`;
      if (size === peak[0]) s += `<text x="${x + bw / 2}" y="${Y(v) - 6}" text-anchor="middle" style="fill:var(--text)">${fmtInt(v)}</text>`;
    });
    $('distChart').innerHTML = s + '</svg>';
  }

  $('distTabs').innerHTML = D.datasets.map((d, i) =>
    `<button role="tab" data-id="${d.id}" aria-selected="${i === 0}">${d.name}</button>`).join('');
  $('distTabs').addEventListener('click', (e) => {
    const b = e.target.closest('button');
    if (!b) return;
    for (const x of $('distTabs').children) x.setAttribute('aria-selected', x === b);
    distChart(b.dataset.id);
  });

  // ---------- boot ----------

  readColors();
  timeChart();
  distChart(D.datasets[0].id);
  newGraph();
  window.addEventListener('resize', draw);
  window.matchMedia('(prefers-color-scheme: dark)').addEventListener('change', () => { readColors(); draw(); });
})();
