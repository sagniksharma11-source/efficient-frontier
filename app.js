(function () {
'use strict';

/* ---------- helpers ---------- */
var $ = function (id) { return document.getElementById(id); };
var K = 252;
var PM = { '6M': 6, '1Y': 12, '3Y': 36, '5Y': 60 };
var MON = ['Jan','Feb','Mar','Apr','May','Jun','Jul','Aug','Sep','Oct','Nov','Dec'];
var D, DATES, N, R = {}, MKT = [], MKTL = [], CUR = null;
var st = { a: 'SUNPHARMA', b: 'MAXHEALTH', period: '3Y', wA: 50, tRisk: '', tRet: '', amount: 100000, sector: 'All', q: '', cStock: 'a', cWin: '6M', rollWin: 90, tStock: 'a' };

function esc(s) { return String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;'); }
function nf(x, d) { d = d == null ? 2 : d; return isFinite(x) && x !== null ? x.toLocaleString('en-IN', { minimumFractionDigits: d, maximumFractionDigits: d }) : 'n/a'; }
function inr(x, d) { return isFinite(x) ? '₹' + nf(x, d == null ? 2 : d) : 'n/a'; }
function pc(x, d, sign) { d = d == null ? 2 : d; return isFinite(x) ? ((sign && x > 0 ? '+' : '') + (x * 100).toFixed(d) + '%') : 'n/a'; }
function fdate(iso) { return iso.slice(8, 10) + '-' + MON[+iso.slice(5, 7) - 1] + '-' + iso.slice(0, 4); }
function fmon(iso) { return MON[+iso.slice(5, 7) - 1] + ' ' + iso.slice(2, 4); }
function mean(a) { var s = 0; for (var i = 0; i < a.length; i++) s += a[i]; return s / a.length; }
function cov(a, b) { var ma = mean(a), mb = mean(b), s = 0; for (var i = 0; i < a.length; i++) s += (a[i] - ma) * (b[i] - mb); return s / (a.length - 1); }
function sd(a) { return Math.sqrt(cov(a, a)); }
function moments(a) { var m = mean(a), m2 = 0, m3 = 0, m4 = 0; a.forEach(function (x) { var d = x - m; m2 += d * d; m3 += d * d * d; m4 += d * d * d * d; }); var n = a.length; m2 /= n; m3 /= n; m4 /= n; return { skew: m3 / Math.pow(m2, 1.5), kurt: m4 / (m2 * m2) - 3 }; }
function rollStd(r, w) { var o = new Array(r.length).fill(NaN); for (var i = w - 1; i < r.length; i++) o[i] = sd(r.slice(i - w + 1, i + 1)); return o; }
function rollCorr(a, b, w) { var o = new Array(a.length).fill(NaN); for (var i = w - 1; i < a.length; i++) { var x = a.slice(i - w + 1, i + 1), y = b.slice(i - w + 1, i + 1); o[i] = cov(x, y) / (sd(x) * sd(y)); } return o; }
function sma(c, w) { var o = new Array(c.length).fill(NaN), s = 0; for (var i = 0; i < c.length; i++) { s += c[i]; if (i >= w) s -= c[i - w]; if (i >= w - 1) o[i] = s / w; } return o; }
function ema(c, w) { var o = new Array(c.length).fill(NaN), k = 2 / (w + 1), e = null; for (var i = 0; i < c.length; i++) { if (i === w - 1) { e = mean(c.slice(0, w)); o[i] = e; } else if (i >= w) { e = c[i] * k + e * (1 - k); o[i] = e; } } return o; }
function rsi(c, w) {
  var o = new Array(c.length).fill(NaN), g = 0, l = 0;
  for (var i = 1; i < c.length; i++) {
    var d = c[i] - c[i - 1], up = Math.max(d, 0), dn = Math.max(-d, 0);
    if (i <= w) { g += up; l += dn; if (i === w) { g /= w; l /= w; o[i] = l === 0 ? 100 : 100 - 100 / (1 + g / l); } }
    else { g = (g * (w - 1) + up) / w; l = (l * (w - 1) + dn) / w; o[i] = l === 0 ? 100 : 100 - 100 / (1 + g / l); }
  }
  return o;
}
function macd(c) {
  var e12 = ema(c, 12), e26 = ema(c, 26), line = c.map(function (_, i) { return e12[i] - e26[i]; });
  var first = line.findIndex(function (x) { return isFinite(x); });
  var sig = new Array(c.length).fill(NaN);
  if (first >= 0) { var part = ema(line.slice(first), 9); for (var i = 0; i < part.length; i++) sig[first + i] = part[i]; }
  return { line: line, sig: sig, hist: line.map(function (x, i) { return x - sig[i]; }) };
}
function niceDomain(lo, hi, count, floor0) {
  if (!(hi > lo)) { lo -= 1; hi += 1; }
  var raw = (hi - lo) / count, p = Math.pow(10, Math.floor(Math.log10(raw))), f = raw / p;
  var step = (f < 1.5 ? 1 : f < 3 ? 2 : f < 7 ? 5 : 10) * p;
  var min = Math.floor(lo / step + 1e-9) * step, max = Math.ceil(hi / step - 1e-9) * step;
  if (floor0 && min < 0) min = 0;
  var t = []; for (var v = min; v <= max + step * 1e-9; v += step) t.push(+v.toFixed(10));
  return { min: min, max: max, ticks: t };
}
function cutoffIdx(months) {
  var d = new Date(DATES[N - 1] + 'T00:00:00Z'); d.setUTCMonth(d.getUTCMonth() - months);
  var iso = d.toISOString().slice(0, 10);
  if (iso < DATES[0]) return -1;
  var lo = 0, hi = N - 1;
  while (lo < hi) { var mid = (lo + hi + 1) >> 1; if (DATES[mid] <= iso) lo = mid; else hi = mid - 1; }
  return lo;
}
function meta(sym) { return D.universe.find(function (u) { return u.symbol === sym; }); }

/* ---------- data prep ---------- */
function prep() {
  DATES = D.dates; N = DATES.length;
  var syms = Object.keys(D.stocks);
  syms.forEach(function (s) { var c = D.stocks[s].c, r = []; for (var i = 1; i < N; i++) r.push(c[i] / c[i - 1] - 1); R[s] = r; });
  for (var i = 0; i < N - 1; i++) { var t = 0; syms.forEach(function (s) { t += R[s][i]; }); MKT.push(t / syms.length); }
  MKTL = [1]; MKT.forEach(function (r, i) { MKTL.push(MKTL[i] * (1 + r)); });
  D.nStocks = syms.length;
}

/* ---------- analysis ---------- */
function analyse() {
  var base = Math.max(0, cutoffIdx(PM[st.period]));
  var info = ['a', 'b'].map(function (k) {
    var sym = st[k], S = D.stocks[sym], r = R[sym].slice(base), c = S.c.slice(base);
    var peak = c[0], mdd = 0; c.forEach(function (x) { peak = Math.max(peak, x); mdd = Math.min(mdd, x / peak - 1); });
    var m = MKT.slice(base);
    return { k: k, sym: sym, S: S, r: r, c: c, mu: mean(r) * K, sig: sd(r) * Math.sqrt(K), mdd: mdd, beta: cov(r, m) / cov(m, m), total: c[c.length - 1] / c[0] - 1, meta: meta(sym) };
  });
  var A = info[0], B = info[1], cv = cov(A.r, B.r) * K, corr = cv / (A.sig * B.sig);
  function port(w) { var v = w * w * A.sig * A.sig + (1 - w) * (1 - w) * B.sig * B.sig + 2 * w * (1 - w) * cv; return { w: w, mu: w * A.mu + (1 - w) * B.mu, sd: Math.sqrt(Math.max(v, 0)) }; }
  var den = A.sig * A.sig + B.sig * B.sig - 2 * cv, wm = den > 1e-12 ? (B.sig * B.sig - cv) / den : 0.5;
  wm = Math.min(1, Math.max(0, wm));
  var upIsA = A.mu >= B.mu;
  function eff(w) { return upIsA ? w >= wm - 1e-9 : w <= wm + 1e-9; }
  var ws = []; for (var i = 0; i <= 200; i++) ws.push(i / 200); ws.push(wm); ws.sort(function (x, y) { return x - y; });
  var pts = ws.map(function (w) { var p = port(w); p.eff = eff(w); return p; });
  return { base: base, A: A, B: B, cv: cv, corr: corr, port: port, wm: wm, mvp: port(wm), pts: pts, hiW: upIsA ? 1 : 0, nObs: A.r.length };
}
function targetRisk(M, t) {
  var mv = M.mvp, pe = M.port(M.hiW);
  if (t < mv.sd - 1e-9) return { ok: false, min: mv.sd };
  if (t >= pe.sd) return { ok: true, w: M.hiW, capped: true };
  var lo = M.wm, up = M.hiW;
  for (var i = 0; i < 80; i++) { var mid = (lo + up) / 2; if (M.port(mid).sd < t) lo = mid; else up = mid; }
  return { ok: true, w: (lo + up) / 2 };
}
function targetReturn(M, t) {
  var lo = Math.min(M.A.mu, M.B.mu), hi = Math.max(M.A.mu, M.B.mu);
  if (t < lo - 1e-12 || t > hi + 1e-12) return { ok: false, lo: lo, hi: hi };
  if (t <= M.mvp.mu || Math.abs(M.A.mu - M.B.mu) < 1e-12) return { ok: true, w: M.wm, mvp: true };
  return { ok: true, w: (t - M.B.mu) / (M.A.mu - M.B.mu) };
}

/* ---------- chart plumbing ---------- */
function tipEl(el) { var t = el.querySelector('.tip'); if (!t) { t = document.createElement('div'); t.className = 'tip'; t.hidden = true; el.appendChild(t); } return t; }
function showTip(el, html, px, py, W) {
  var t = tipEl(el); t.innerHTML = html; t.hidden = false;
  var w = t.offsetWidth; t.style.left = Math.max(0, Math.min(px + 14, W - w)) + 'px'; t.style.top = Math.max(0, py - 10) + 'px';
}
function hideTip(el) { var t = el.querySelector('.tip'); if (t) t.hidden = true; }
function xTicks(x, n, pw, ml) {
  var out = '', cnt = pw < 420 ? 3 : 5;
  for (var k = 0; k < cnt; k++) {
    var i = Math.round(k * (n - 1) / (cnt - 1)), xx = ml + (n < 2 ? 0 : i / (n - 1) * pw);
    out += '<text class="tx" x="' + xx.toFixed(1) + '" text-anchor="' + (k === 0 ? 'start' : k === cnt - 1 ? 'end' : 'middle') + '">' + fmon(x[i]) + '</text>';
  }
  return out;
}
function mountSvg(el, W, H, inner) {
  var keep = el.querySelector('.tip'); el.innerHTML = '<svg viewBox="0 0 ' + W + ' ' + H + '" width="' + W + '" height="' + H + '" role="img">' + inner + '</svg>';
  if (keep) el.appendChild(keep);
  return el.querySelector('svg');
}
function pathOf(vals, X, Y) {
  var d = '', pen = false;
  vals.forEach(function (v, i) { if (!isFinite(v)) { pen = false; return; } d += (pen ? 'L' : 'M') + X(i).toFixed(1) + ' ' + Y(v).toFixed(1); pen = true; });
  return d;
}
function legendHtml(items) { return items.map(function (it) { return '<span><svg width="22" height="10" aria-hidden="true"><line x1="0" y1="5" x2="22" y2="5" style="stroke:' + it.color + ';stroke-width:2' + (it.dash ? ';stroke-dasharray:4 3' : '') + '"/></svg>' + esc(it.name) + '</span>'; }).join(''); }

/* generic multi-line chart */
function drawLine(el, o) {
  var W = Math.max(260, el.clientWidth), H = o.h || 260, m = { l: o.ml || 50, r: 10, t: 8, b: 22 };
  var n = o.x.length, pw = W - m.l - m.r, ph = H - m.t - m.b, lo = Infinity, hi = -Infinity;
  function scan(v) { if (isFinite(v)) { if (v < lo) lo = v; if (v > hi) hi = v; } }
  o.series.forEach(function (s) { s.vals.forEach(scan); });
  if (o.bars) { o.bars.vals.forEach(scan); scan(0); }
  if (o.yMin != null) lo = o.yMin; if (o.yMax != null) hi = o.yMax;
  var dom = niceDomain(lo, hi, 4);
  if (o.yMin != null) dom.min = o.yMin; if (o.yMax != null) dom.max = o.yMax;
  var X = function (i) { return m.l + (n < 2 ? 0 : i / (n - 1) * pw); };
  var Y = function (v) { return m.t + ph - (v - dom.min) / (dom.max - dom.min) * ph; };
  var s = '';
  dom.ticks.forEach(function (t) { if (t < dom.min - 1e-9 || t > dom.max + 1e-9) return; var y = Y(t); s += '<line class="gr" x1="' + m.l + '" x2="' + (W - m.r) + '" y1="' + y.toFixed(1) + '" y2="' + y.toFixed(1) + '"/><text class="tx" x="' + (m.l - 6) + '" y="' + (y + 4).toFixed(1) + '" text-anchor="end">' + (o.yFmt ? o.yFmt(t) : t) + '</text>'; });
  (o.refs || []).forEach(function (rf) { var y = Y(rf); s += '<line class="ax" x1="' + m.l + '" x2="' + (W - m.r) + '" y1="' + y.toFixed(1) + '" y2="' + y.toFixed(1) + '" style="stroke-dasharray:4 3"/>'; });
  if (o.bars) { var bw = Math.max(1, pw / n * 0.7), y0 = Y(0); o.bars.vals.forEach(function (v, i) { if (!isFinite(v)) return; var y = Y(v); s += '<rect x="' + (X(i) - bw / 2).toFixed(1) + '" y="' + Math.min(y, y0).toFixed(1) + '" width="' + bw.toFixed(1) + '" height="' + Math.max(0.5, Math.abs(y - y0)).toFixed(1) + '" style="fill:' + o.bars.color + ';opacity:.55"/>'; }); }
  o.series.forEach(function (sr) { s += '<path d="' + pathOf(sr.vals, X, Y) + '" fill="none" style="stroke:' + sr.color + ';stroke-width:' + (sr.w || 1.6) + (sr.dash ? ';stroke-dasharray:5 3' : '') + '" stroke-linejoin="round"/>'; });
  s += '<g transform="translate(0,' + (H - 6) + ')">' + xTicks(o.x, n, pw, m.l) + '</g>';
  s += '<line class="cross" id="x" y1="' + m.t + '" y2="' + (m.t + ph) + '" style="display:none"/><rect x="' + m.l + '" y="' + m.t + '" width="' + pw + '" height="' + ph + '" fill="transparent"/>';
  var svg = mountSvg(el, W, H, s), cross = svg.querySelector('.cross'), rect = svg.querySelector('rect:last-of-type');
  function move(e) {
    var b = svg.getBoundingClientRect(), px = (e.clientX - b.left) * (W / b.width), i = Math.max(0, Math.min(n - 1, Math.round((px - m.l) / pw * (n - 1))));
    cross.setAttribute('x1', X(i)); cross.setAttribute('x2', X(i)); cross.style.display = '';
    var f = o.tipFmt || function (v) { return nf(v, 2); };
    var h = '<b>' + fdate(o.x[i]) + '</b>';
    o.series.forEach(function (sr) { if (isFinite(sr.vals[i])) h += '<br><span style="color:var(--muted)">' + esc(sr.name) + '</span> ' + f(sr.vals[i]); });
    if (o.bars && isFinite(o.bars.vals[i])) h += '<br><span style="color:var(--muted)">' + esc(o.bars.name) + '</span> ' + f(o.bars.vals[i]);
    showTip(el, h, X(i) * (b.width / W), e.clientY - b.top, b.width);
  }
  rect.addEventListener('pointermove', move); rect.addEventListener('pointerleave', function () { cross.style.display = 'none'; hideTip(el); });
}

/* ---------- list of stocks ---------- */
function renderList() {
  var q = st.q.trim().toLowerCase(), rows = '', shown = 0;
  D.universe.forEach(function (u) {
    if (st.sector !== 'All' && u.sector !== st.sector) return;
    if (q && u.symbol.toLowerCase().indexOf(q) < 0 && u.name.toLowerCase().indexOf(q) < 0) return;
    shown++;
    var sel = (u.symbol === st.a ? 'A' : u.symbol === st.b ? 'B' : ''), btn = '', last = '<td class="num"></td><td class="num"></td>';
    if (u.hasData) {
      var S = D.stocks[u.symbol].last, ch = S.close / S.prev - 1;
      last = '<td class="num">' + nf(S.close, 2) + '</td><td class="num">' + pc(ch, 2, true) + '</td>';
      if (sel) btn = '<button type="button" data-act="rm" data-sym="' + esc(u.symbol) + '">Remove ' + sel + '</button>';
      else if (st.a && st.b) btn = '<button type="button" disabled>Two selected</button>';
      else btn = '<button type="button" data-act="add" data-sym="' + esc(u.symbol) + '">Add as ' + (st.a ? 'B' : 'A') + '</button>';
    } else btn = '<span class="small">No price data supplied</span>';
    rows += '<tr class="' + (u.hasData ? '' : 'off') + '"><td><b>' + esc(u.symbol) + '</b></td><td>' + esc(u.name) + '</td><td>' + esc(u.sector) + '</td>' + last + '<td class="num">' + btn + '</td></tr>';
  });
  $('stocks').innerHTML = rows || '<tr><td colspan="6" class="muted">No stocks match.</td></tr>';
  $('listcount').textContent = shown + ' of ' + D.universe.length + ' stocks shown.';
  ['a', 'b'].forEach(function (k) {
    var u = st[k] && meta(st[k]), K2 = k.toUpperCase();
    $('slot' + K2).textContent = u ? u.symbol + ', ' + u.name : 'None selected'; $('slot' + K2).className = u ? '' : 'muted';
    $('rm' + K2).hidden = !u;
  });
  $('limitmsg').textContent = st.a && st.b ? 'Two stocks selected. Remove one to choose a different stock.' : 'Two stocks at most. The same stock cannot be chosen twice. Stocks from different sectors can be compared.';
}

/* ---------- results ---------- */
function twoCol(rows, hdrs) {
  return '<thead><tr><th></th>' + hdrs.map(function (h) { return '<th class="num">' + h + '</th>'; }).join('') + '</tr></thead><tbody>' +
    rows.map(function (r) { return '<tr><td class="lbl">' + r[0] + '</td>' + r.slice(1).map(function (c) { return '<td class="num">' + c + '</td>'; }).join('') + '</tr>'; }).join('') + '</tbody>';
}
function hdrAB(M) { return ['<span class="sw a"></span>' + esc(M.A.sym), '<span class="sw b"></span>' + esc(M.B.sym)]; }

function renderAll() {
  renderList();
  var ready = st.a && st.b;
  $('empty').hidden = !!ready; $('results').hidden = !ready;
  if (!ready) { CUR = null; return; }
  CUR = analyse();
  renderAlerts(); renderPortfolio(); renderSnapshot(); renderFund(); renderPerf(); renderRisk(); renderCharts();
}

function renderAlerts() {
  var M = CUR, out = [], days = Math.floor((Date.now() - Date.parse(DATES[N - 1] + 'T00:00:00Z')) / 86400000);
  if (days > 4) out.push(['warn', 'Stale prices', 'The latest price in the supplied files is dated ' + fdate(DATES[N - 1]) + ', which is ' + days + ' days ago. This site reads the supplied files and has no live feed.']);
  if (M.nObs < 60) out.push(['warn', 'Short history', 'Only ' + M.nObs + ' daily returns are in the selected period. Estimates of risk and correlation are unreliable below about 60.']);
  [M.A, M.B].forEach(function (X) {
    var gaps = 0, zero = 0, v = X.S.v;
    for (var i = M.base + 1; i < N; i++) { var d = (Date.parse(DATES[i]) - Date.parse(DATES[i - 1])) / 86400000; if (d > 6) gaps++; if (v[i] === 0) zero++; }
    if (gaps) out.push(['warn', 'Missing days', X.sym + ' has ' + gaps + ' gaps longer than 6 calendar days in the selected period.']);
    if (zero) out.push(['warn', 'No volume', X.sym + ' shows zero traded volume on ' + zero + ' days.']);
    X.S.actions.forEach(function (a) { if (a.date > DATES[M.base]) out.push(['note', 'Adjusted', X.sym + ': ' + a.note + ' on ' + fdate(a.date) + '. Earlier prices and volumes were restated so returns are not distorted.']); });
  });
  if (!out.some(function (o) { return o[0] === 'warn'; })) out.unshift(['note', 'Checked', 'No missing or stale prices found. ' + M.nObs + ' daily returns from ' + fdate(DATES[M.base]) + ' to ' + fdate(DATES[N - 1]) + '.']);
  $('alerts').innerHTML = out.map(function (o) { return '<li class="' + o[0] + '"><b>' + (o[0] === 'warn' ? 'Warning' : 'Note') + '</b> ' + esc(o[2]) + '</li>'; }).join('');
}

function renderPortfolio() {
  var M = CUR; if (!M) return;
  var w = st.wA / 100;
  $('wAval').textContent = '(' + M.A.sym + '): ' + st.wA + '%'; $('wBval').textContent = 'Stock B (' + M.B.sym + ') receives the remaining ' + (100 - st.wA) + '%';
  $('fdesc').textContent = 'Each point is a mix of ' + M.A.sym + ' and ' + M.B.sym + ' with no short selling. Weights run from 100% ' + M.B.sym + ' to 100% ' + M.A.sym + '. Returns and risk are annualised from ' + st.period.replace('M', ' months').replace('Y', ' years').replace('1 years', '1 year') + ' of daily prices.';
  var sel = M.port(w), cols = [{ n: 'Selected allocation', p: sel }, { n: 'Minimum variance', p: M.mvp }], msgs = [];
  var tr = null, tt = null;
  if (st.tRisk !== '' && isFinite(+st.tRisk)) {
    var r = targetRisk(M, +st.tRisk / 100);
    if (r.ok) { tr = M.port(r.w); cols.push({ n: 'Target risk ' + (+st.tRisk).toFixed(1) + '%', p: tr }); if (r.capped) msgs.push('Target risk: ' + st.tRisk + '% is above the risk of holding only ' + (M.hiW ? M.A.sym : M.B.sym) + ', so that is the highest-return choice available.'); }
    else msgs.push('Target risk: ' + st.tRisk + '% is below the lowest volatility these two stocks can reach together, which is ' + pc(r.min, 2) + '.');
  }
  if (st.tRet !== '' && isFinite(+st.tRet)) {
    var q = targetReturn(M, +st.tRet / 100);
    if (q.ok) { tt = M.port(q.w); cols.push({ n: 'Target return ' + (+st.tRet).toFixed(1) + '%', p: tt }); if (q.mvp) msgs.push('Target return: the minimum variance portfolio already earns ' + pc(M.mvp.mu, 2) + ', which is above the target, so it is shown as the lowest-risk choice.'); }
    else msgs.push('Target return: ' + st.tRet + '% is outside the range of returns these two stocks offer without short selling or leverage (' + pc(q.lo, 2) + ' to ' + pc(q.hi, 2) + ').');
  }
  var amt = +st.amount > 0 ? +st.amount : 0;
  var rows = [
    ['Weight in ' + esc(M.A.sym)].concat(cols.map(function (c) { return pc(c.p.w, 1); })),
    ['Weight in ' + esc(M.B.sym)].concat(cols.map(function (c) { return pc(1 - c.p.w, 1); })),
    ['Expected return a year'].concat(cols.map(function (c) { return pc(c.p.mu, 2); })),
    ['Volatility a year'].concat(cols.map(function (c) { return pc(c.p.sd, 2); }))
  ];
  if (amt) {
    var pa = M.A.S.last.close, pb = M.B.S.last.close;
    rows.push(['Amount in ' + esc(M.A.sym)].concat(cols.map(function (c) { return inr(amt * c.p.w, 0); })));
    rows.push(['Amount in ' + esc(M.B.sym)].concat(cols.map(function (c) { return inr(amt * (1 - c.p.w), 0); })));
    rows.push(['Whole shares of ' + esc(M.A.sym)].concat(cols.map(function (c) { return nf(Math.floor(amt * c.p.w / pa), 0); })));
    rows.push(['Whole shares of ' + esc(M.B.sym)].concat(cols.map(function (c) { return nf(Math.floor(amt * (1 - c.p.w) / pb), 0); })));
  }
  $('ptable').innerHTML = twoCol(rows, cols.map(function (c) { return esc(c.n); }));
  var wavg = w * M.A.sig + (1 - w) * M.B.sig;
  msgs.unshift('Selected allocation: the weighted average of the two stocks\' volatilities is ' + pc(wavg, 2) + ' and the portfolio volatility is ' + pc(sel.sd, 2) + ', a difference of ' + pc(wavg - sel.sd, 2) + ' from diversification.' + (amt ? ' Whole share counts use the last close and leave a small cash remainder.' : ''));
  $('pmsg').innerHTML = msgs.map(function (t) { return '<p>' + esc(t) + '</p>'; }).join('');
  drawFrontier($('cFrontier'), M, sel, tr, tt);
  M.sel = sel; M.tr = tr; M.tt = tt; M.cols = cols;
}

function drawFrontier(el, M, sel, tr, tt) {
  var W = Math.max(280, el.clientWidth), H = Math.round(Math.min(420, Math.max(300, W * 0.55))), m = { l: 54, r: 16, t: 14, b: 42 };
  var xs = M.pts.map(function (p) { return p.sd * 100; }), ys = M.pts.map(function (p) { return p.mu * 100; });
  var xl = Math.min.apply(null, xs), xh = Math.max.apply(null, xs), yl = Math.min.apply(null, ys), yh = Math.max.apply(null, ys);
  var px = (xh - xl) * 0.06 || 1, py = (yh - yl) * 0.12 || 1;
  var dx = niceDomain(xl - px, xh + px, 5, true), dy = niceDomain(yl - py, yh + py, 5, false);
  var pw = W - m.l - m.r, ph = H - m.t - m.b;
  var X = function (v) { return m.l + (v - dx.min) / (dx.max - dx.min) * pw; }, Y = function (v) { return m.t + ph - (v - dy.min) / (dy.max - dy.min) * ph; };
  var s = '';
  dx.ticks.forEach(function (t) { var x = X(t); s += '<line class="gr" x1="' + x.toFixed(1) + '" x2="' + x.toFixed(1) + '" y1="' + m.t + '" y2="' + (m.t + ph) + '"/><text class="tx" x="' + x.toFixed(1) + '" y="' + (H - 24) + '" text-anchor="middle">' + t + '</text>'; });
  dy.ticks.forEach(function (t) { var y = Y(t); s += '<line class="gr" x1="' + m.l + '" x2="' + (W - m.r) + '" y1="' + y.toFixed(1) + '" y2="' + y.toFixed(1) + '"/><text class="tx" x="' + (m.l - 6) + '" y="' + (y + 4).toFixed(1) + '" text-anchor="end">' + t + '</text>'; });
  s += '<line class="ax" x1="' + m.l + '" x2="' + (W - m.r) + '" y1="' + (m.t + ph) + '" y2="' + (m.t + ph) + '"/><line class="ax" x1="' + m.l + '" x2="' + m.l + '" y1="' + m.t + '" y2="' + (m.t + ph) + '"/>';
  s += '<text class="tx" x="' + (m.l + pw / 2) + '" y="' + (H - 6) + '" text-anchor="middle">Annualised volatility (%)</text><text class="tx" transform="translate(12,' + (m.t + ph / 2) + ') rotate(-90)" text-anchor="middle">Annualised expected return (%)</text>';
  var dE = '', dI = '';
  for (var i = 0; i < M.pts.length - 1; i++) {
    var p = M.pts[i], q = M.pts[i + 1], seg = 'M' + X(p.sd * 100).toFixed(1) + ' ' + Y(p.mu * 100).toFixed(1) + 'L' + X(q.sd * 100).toFixed(1) + ' ' + Y(q.mu * 100).toFixed(1);
    if (p.eff && q.eff) dE += seg; else dI += seg;
  }
  s += '<path d="' + dI + '" fill="none" style="stroke:var(--muted);stroke-width:1.5;stroke-dasharray:4 3"/><path d="' + dE + '" fill="none" style="stroke:var(--fg);stroke-width:2.5" stroke-linejoin="round"/>';
  function labAway(p, nb, t) {
    var x = X(p.sd * 100), y = Y(p.mu * 100), vx = X(nb.sd * 100) - x, vy = Y(nb.mu * 100) - y, L = Math.sqrt(vx * vx + vy * vy) || 1, ox = -vx / L * 12, oy = -vy / L * 12;
    var right = ox >= 0; if (Math.abs(ox) < 4) right = x < W * 0.6;
    if (right && x + 12 + t.length * 7.2 > W - 4) return '<text class="tl" x="' + (x + 4).toFixed(1) + '" y="' + (y - 12).toFixed(1) + '" text-anchor="end">' + esc(t) + '</text>';
    return '<text class="tl" x="' + (x + (right ? 10 : -10) + ox * 0.3).toFixed(1) + '" y="' + (y + oy * 0.8 + 4).toFixed(1) + '" text-anchor="' + (right ? 'start' : 'end') + '">' + esc(t) + '</text>';
  }
  var a = M.port(1), b = M.port(0), ax = X(a.sd * 100), ay = Y(a.mu * 100), bx = X(b.sd * 100), by = Y(b.mu * 100), mx = X(M.mvp.sd * 100), my = Y(M.mvp.mu * 100), sx = X(sel.sd * 100), sy = Y(sel.mu * 100);
  var nbA = M.pts[M.pts.length - 2], nbB = M.pts[1];
  s += '<circle cx="' + ax + '" cy="' + ay + '" r="6" style="fill:var(--sa);stroke:var(--surface);stroke-width:2"/>' + labAway(a, nbA, 'A ' + M.A.sym);
  s += '<circle cx="' + bx + '" cy="' + by + '" r="6" style="fill:var(--sb);stroke:var(--surface);stroke-width:2"/>' + labAway(b, nbB, 'B ' + M.B.sym);
  var mleft = mx - m.l > 50;
  s += '<rect x="' + (mx - 5) + '" y="' + (my - 5) + '" width="10" height="10" style="fill:var(--surface);stroke:var(--fg);stroke-width:2"/><text class="tl" x="' + (mleft ? mx - 10 : mx + 10) + '" y="' + (my + 4) + '" text-anchor="' + (mleft ? 'end' : 'start') + '">MVP</text>';
  if (tr) { var tx = X(tr.sd * 100), ty = Y(tr.mu * 100); s += '<path d="M' + tx + ' ' + (ty - 7) + 'L' + (tx + 7) + ' ' + (ty + 5) + 'L' + (tx - 7) + ' ' + (ty + 5) + 'Z" style="fill:var(--surface);stroke:var(--fg);stroke-width:2"/>'; }
  if (tt) { var ux = X(tt.sd * 100), uy = Y(tt.mu * 100); s += '<path d="M' + ux + ' ' + (uy - 7) + 'L' + (ux + 7) + ' ' + uy + 'L' + ux + ' ' + (uy + 7) + 'L' + (ux - 7) + ' ' + uy + 'Z" style="fill:var(--surface);stroke:var(--fg);stroke-width:2"/>'; }
  s += '<circle cx="' + sx + '" cy="' + sy + '" r="6" style="fill:var(--fg);stroke:var(--surface);stroke-width:2"/>' + '<text class="tl" x="' + (sx > W * 0.7 ? sx - 10 : sx + 10) + '" y="' + (sy + 18) + '" text-anchor="' + (sx > W * 0.7 ? 'end' : 'start') + '">Selected</text>';
  s += '<circle id="hov" r="5" style="display:none;fill:none;stroke:var(--fg);stroke-width:2"/><rect x="' + m.l + '" y="' + m.t + '" width="' + pw + '" height="' + ph + '" fill="transparent"/>';
  var svg = mountSvg(el, W, H, s), hov = svg.querySelector('#hov'), rect = svg.querySelector('rect:last-of-type');
  rect.addEventListener('pointermove', function (e) {
    var bb = svg.getBoundingClientRect(), k = W / bb.width, mx2 = (e.clientX - bb.left) * k, my2 = (e.clientY - bb.top) * k, best = null, bd = 1e9;
    M.pts.forEach(function (p) { var d = Math.pow(X(p.sd * 100) - mx2, 2) + Math.pow(Y(p.mu * 100) - my2, 2); if (d < bd) { bd = d; best = p; } });
    hov.setAttribute('cx', X(best.sd * 100)); hov.setAttribute('cy', Y(best.mu * 100)); hov.style.display = '';
    showTip(el, '<b>' + pc(best.w, 1) + ' ' + esc(M.A.sym) + ', ' + pc(1 - best.w, 1) + ' ' + esc(M.B.sym) + '</b><br>Return ' + pc(best.mu, 2) + '<br>Volatility ' + pc(best.sd, 2) + '<br>' + (best.eff ? 'Efficient' : 'Inefficient: same risk, higher return exists'), X(best.sd * 100) / k, Y(best.mu * 100) / k, bb.width);
  });
  rect.addEventListener('pointerleave', function () { hov.style.display = 'none'; hideTip(el); });
  var ic = function (shape) { return '<svg width="16" height="14" aria-hidden="true">' + shape + '</svg>'; };
  $('fleg').innerHTML =
    '<span><svg width="22" height="10" aria-hidden="true"><line x1="0" y1="5" x2="22" y2="5" style="stroke:var(--fg);stroke-width:2.5"/></svg>Efficient frontier</span>' +
    '<span><svg width="22" height="10" aria-hidden="true"><line x1="0" y1="5" x2="22" y2="5" style="stroke:var(--muted);stroke-width:1.5;stroke-dasharray:4 3"/></svg>Inefficient branch</span>' +
    '<span>' + ic('<circle cx="8" cy="7" r="5" style="fill:var(--sa)"/>') + 'Stock A</span><span>' + ic('<circle cx="8" cy="7" r="5" style="fill:var(--sb)"/>') + 'Stock B</span>' +
    '<span>' + ic('<rect x="3" y="2" width="10" height="10" style="fill:none;stroke:var(--fg);stroke-width:2"/>') + 'Minimum variance</span>' +
    '<span>' + ic('<circle cx="8" cy="7" r="5" style="fill:var(--fg)"/>') + 'Selected allocation</span>' +
    (tr ? '<span>' + ic('<path d="M8 1L14 12L2 12Z" style="fill:none;stroke:var(--fg);stroke-width:2"/>') + 'Target risk</span>' : '') +
    (tt ? '<span>' + ic('<path d="M8 1L14 7L8 13L2 7Z" style="fill:none;stroke:var(--fg);stroke-width:2"/>') + 'Target return</span>' : '');
}

function renderSnapshot() {
  var M = CUR, hd = hdrAB(M), c52 = cutoffIdx(12);
  function col(X) {
    var L = X.S.last, S = X.S, lo = Infinity, hi = -Infinity;
    for (var i = Math.max(0, c52); i < N; i++) { if (S.h[i] > hi) hi = S.h[i]; if (S.l[i] < lo) lo = S.l[i]; }
    return { L: L, hi: hi, lo: lo, ch: L.close - L.prev, pc: L.close / L.prev - 1 };
  }
  var a = col(M.A), b = col(M.B);
  var rows = [
    ['Last price (close of ' + fdate(DATES[N - 1]) + ')', inr(a.L.close), inr(b.L.close)],
    ['Daily change (₹)', (a.ch > 0 ? '+' : '') + nf(a.ch, 2), (b.ch > 0 ? '+' : '') + nf(b.ch, 2)],
    ['Daily change (%)', pc(a.pc, 2, true), pc(b.pc, 2, true)],
    ['Previous close', inr(a.L.prev), inr(b.L.prev)],
    ['Open', inr(a.L.open), inr(b.L.open)],
    ['Day high', inr(a.L.high), inr(b.L.high)],
    ['Day low', inr(a.L.low), inr(b.L.low)],
    ['Traded volume (shares)', nf(a.L.qty, 0), nf(b.L.qty, 0)],
    ['52-week high', inr(a.hi), inr(b.hi)],
    ['52-week low', inr(a.lo), inr(b.lo)],
    ['Market capitalisation (₹ crore)', fv(fundFor(M.A.sym), FUND[6]), fv(fundFor(M.B.sym), FUND[6])]
  ];
  $('tSnap').innerHTML = twoCol(rows, hd);
}

var FUND = [['pe', 'P/E ratio', 2], ['pb', 'P/B ratio', 2], ['eps', 'EPS (₹)', 2], ['dy', 'Dividend yield (%)', 2], ['roe', 'ROE (%)', 2], ['de', 'Debt-to-equity', 2], ['mcap', 'Market capitalisation (₹ crore)', 0]];
var FCOLS = ['pat', 'pref_div', 'wtd_shares', 'equity', 'avg_equity', 'debt', 'shares_out', 'dps'];
var FORMULAS = [
  ['P/E ratio', 'Current market price (CMP) ÷ EPS'],
  ['P/B ratio', 'CMP ÷ book value per share (equity ÷ shares outstanding)'],
  ['EPS', '(Net profit after tax − preference dividend) ÷ weighted average outstanding equity shares'],
  ['Dividend yield (%)', '(Annual dividend per share ÷ CMP) × 100'],
  ['ROE (%)', '(Net profit after tax ÷ average shareholders\' equity) × 100'],
  ['Debt-to-equity', 'Total debt ÷ total shareholders\' equity'],
  ['Market capitalisation', 'CMP × total outstanding shares']
];
function numOr(v) { return typeof v === 'number' && isFinite(v) ? v : null; }
/* Ratios are computed from reported inputs and the last close (CMP) using the formulas above. */
function fundFor(sym) {
  var f = D.fundamentals && D.fundamentals[sym]; if (!f || !D.stocks[sym]) return null;
  var cmp = D.stocks[sym].last.close, g = function (k) { return numOr(f[k]); };
  var pat = g('pat'), pref = g('pref_div') || 0, ws = g('wtd_shares'), eq = g('equity'), aeq = g('avg_equity'), debt = g('debt'), so = g('shares_out'), dps = g('dps'), o = {};
  o.eps = pat != null && ws ? (pat - pref) / ws : null;
  o.pe = o.eps == null ? null : o.eps > 0 ? cmp / o.eps : 'n/m';
  var bv = eq != null && so ? eq / so : null;
  o.pb = bv == null ? null : bv > 0 ? cmp / bv : 'n/m';
  o.dy = dps != null ? dps / cmp * 100 : null;
  o.roe = pat != null && aeq ? pat / aeq * 100 : null;
  o.de = debt != null && eq ? debt / eq : null;
  o.mcap = so != null ? cmp * so : null;
  return o;
}
function fv(o, f) { if (!o || o[f[0]] == null) return 'Not supplied'; return typeof o[f[0]] === 'number' ? nf(o[f[0]], f[2]) : o[f[0]]; }
function renderFund() {
  var M = CUR, fa = fundFor(M.A.sym), fb = fundFor(M.B.sym), any = !!(fa || fb);
  var tools = '<div class="btnrow" style="margin:10px 0"><input id="fundFile" type="file" accept=".csv,text/csv" style="position:absolute;left:-9999px"><label class="filebtn" for="fundFile">Load fundamentals inputs (CSV)</label><button id="btnTpl" type="button">Download CSV template</button></div><div class="status" id="fundStatus" role="status"></div>';
  var msg = '<p class="muted small">P/E, P/B, EPS, dividend yield, ROE, debt-to-equity and market capitalisation need company financials that were not in the supplied price files, so none are estimated. The ratios below are calculated from reported figures and the last close using these formulas. Load a CSV of the inputs (₹ crore for profit, equity and debt, crore shares, ₹ for dividend per share; profit should be trailing twelve months) and every ratio fills in for all 50 stocks.</p>' +
    '<div class="scroll"><table><thead><tr><th>Parameter</th><th>Formula</th></tr></thead><tbody>' + FORMULAS.map(function (r) { return '<tr><td><b>' + r[0] + '</b></td><td>' + r[1] + '</td></tr>'; }).join('') + '</tbody></table></div>';
  var body = '';
  if (any) {
    var rows = FUND.map(function (f) { return [f[1], fv(fa, f), fv(fb, f)]; });
    body = '<h3>Selected stocks</h3><div class="scroll"><table>' + twoCol(rows, hdrAB(M)) + '</table></div>';
    var bars = FUND.filter(function (f) { return f[0] !== 'mcap'; }), nb = 0;
    var ch = bars.map(function (f) {
      var x = fa && typeof fa[f[0]] === 'number' ? fa[f[0]] : null, y = fb && typeof fb[f[0]] === 'number' ? fb[f[0]] : null;
      var mx = Math.max(x != null ? Math.abs(x) : 0, y != null ? Math.abs(y) : 0) || 1;
      function bar(v, c) { return v != null ? '<div style="display:flex;align-items:center;gap:8px"><div class="bar"><i style="width:' + (Math.abs(v) / mx * 100).toFixed(0) + '%;background:' + c + '"></i></div><span class="num">' + nf(v, f[2]) + '</span></div>' : '<span class="muted small">Not supplied</span>'; }
      if (x != null || y != null) nb++;
      return '<tr><td class="lbl" style="width:28%">' + f[1] + '</td><td style="width:36%">' + bar(x, 'var(--sa)') + '</td><td style="width:36%">' + bar(y, 'var(--sb)') + '</td></tr>';
    }).join('');
    $('fundChart').innerHTML = '<div class="scroll"><table><thead><tr><th></th><th>' + hdrAB(M)[0] + '</th><th>' + hdrAB(M)[1] + '</th></tr></thead><tbody>' + ch + '</tbody></table></div><p class="hint">Each row has its own scale, so compare the two stocks within a row, not between rows.</p>';
  } else {
    body = '<p class="muted">No fundamentals loaded yet. Values show as "Not supplied".</p>';
    $('fundChart').innerHTML = '<p class="muted">Not available until fundamentals inputs are loaded. See Fundamental and valuation parameters.</p>';
  }
  $('fundBody').innerHTML = msg + tools + body;
  $('fundFile').onchange = loadFundCsv; $('btnTpl').onclick = function () { saveFile('fundamentals-inputs-template.csv', fundTemplate(), 'text/csv'); };
}
function fundTemplate() {
  var L = ['symbol,' + FCOLS.join(',')];
  D.universe.forEach(function (u) { if (u.hasData) { var f = (D.fundamentals && D.fundamentals[u.symbol]) || {}; L.push(u.symbol + ',' + FCOLS.map(function (k) { return f[k] != null ? f[k] : ''; }).join(',')); } });
  return L.join('\n') + '\n';
}
function parseCsvLine(line) { var out = [], cur = '', q = false; for (var i = 0; i < line.length; i++) { var ch = line[i]; if (q) { if (ch === '"') { if (line[i + 1] === '"') { cur += '"'; i++; } else q = false; } else cur += ch; } else if (ch === '"') q = true; else if (ch === ',') { out.push(cur); cur = ''; } else cur += ch; } out.push(cur); return out; }
function loadFundCsv() {
  var file = this.files && this.files[0]; if (!file) return;
  var rd = new FileReader();
  rd.onload = function () {
    var lines = String(rd.result).replace(/^﻿/, '').split(/\r?\n/).filter(function (l) { return l.trim(); });
    var hdr = parseCsvLine(lines[0]).map(function (h) { return h.trim().toLowerCase(); }), si = hdr.indexOf('symbol'), n = 0, bad = [];
    if (si < 0) { $('fundStatus').textContent = 'The CSV needs a column named symbol. Download the template to see the layout.'; return; }
    D.fundamentals = D.fundamentals || {};
    lines.slice(1).forEach(function (l) {
      var c = parseCsvLine(l), sym = (c[si] || '').trim().toUpperCase();
      if (!D.stocks[sym]) { if (sym) bad.push(sym); return; }
      var o = {}, got = 0;
      FCOLS.forEach(function (k) { var i = hdr.indexOf(k); if (i < 0) return; var t = (c[i] || '').replace(/,/g, '').trim(); if (t === '') return; var v = Number(t); if (isFinite(v)) { o[k] = v; got++; } });
      if (got) { D.fundamentals[sym] = o; n++; }
    });
    $('fundStatus').textContent = 'Loaded inputs for ' + n + ' stocks.' + (bad.length ? ' Ignored unknown tickers: ' + bad.slice(0, 6).join(', ') + '.' : '') + ' Values last until this page is closed.';
    if (CUR) { renderFund(); renderSnapshot(); $('fundStatus').textContent = 'Loaded inputs for ' + n + ' stocks.' + (bad.length ? ' Ignored unknown tickers: ' + bad.slice(0, 6).join(', ') + '.' : '') + ' Values last until this page is closed.'; }
  };
  rd.readAsText(file);
}

function renderPerf() {
  $('perfNote').textContent = 'Price returns, adjusted for splits, bonuses and the Tata Motors demerger. Dividends are not included. NIFTY 50 index data was not in the supplied files, so the benchmark column is an equal-weighted daily average of the ' + D.nStocks + ' stocks that were supplied.';
  var M = CUR, hd = hdrAB(M).concat(['Dataset average']);
  var periods = [['1 month', 1], ['3 months', 3], ['6 months', 6], ['1 year', 12], ['3 years', 36]];
  var sp = { '6M': '6 months', '1Y': '1 year', '3Y': '3 years' }[st.period];
  periods.push(['Selected period (' + sp + ')', PM[st.period]]);
  var rows = periods.map(function (p) {
    var i = cutoffIdx(p[1]);
    if (i < 0) return [p[0], 'n/a', 'n/a', 'n/a'];
    var f = function (c) { return pc(c[N - 1] / c[i] - 1, 2, true); };
    return [p[0], f(M.A.S.c), f(M.B.S.c), f(MKTL)];
  });
  $('tPerf').innerHTML = twoCol(rows, hd);
}

function renderRisk() {
  var M = CUR, a = M.A, b = M.B;
  $('tRisk2').innerHTML = twoCol([
    ['Annualised expected return', pc(a.mu), pc(b.mu)],
    ['Annualised standard deviation', pc(a.sig), pc(b.sig)],
    ['Maximum drawdown', pc(a.mdd), pc(b.mdd)],
    ['Beta versus dataset average', nf(a.beta, 2), nf(b.beta, 2)]
  ], hdrAB(M));
  $('tPair').innerHTML = '<tbody>' +
    [['Covariance (annualised)', nf(M.cv, 4)], ['Correlation coefficient', nf(M.corr, 3)], ['Minimum variance weights', pc(M.wm, 1) + ' ' + esc(a.sym) + ', ' + pc(1 - M.wm, 1) + ' ' + esc(b.sym)], ['Minimum variance volatility', pc(M.mvp.sd)], ['Daily returns used', nf(M.nObs, 0)]]
      .map(function (r) { return '<tr><td class="lbl">' + r[0] + '</td><td class="num">' + r[1] + '</td></tr>'; }).join('') + '</tbody>';
  $('riskNote').textContent = 'Expected return is the mean daily return times 252. Standard deviation and covariance use sample statistics scaled by 252 and the square root of 252. Maximum drawdown is the largest fall from a previous closing high in the selected period. Beta is measured against the equal-weighted daily average of the ' + D.nStocks + ' supplied stocks, which includes the stock itself, because NIFTY 50 index data was not supplied.';
}

/* ---------- supporting charts ---------- */
function renderCharts() {
  var M = CUR, base = M.base, A = M.A, B = M.B, x = DATES.slice(base);
  // indexed
  var ia = A.c.map(function (v) { return v / A.c[0] * 100; }), ib = B.c.map(function (v) { return v / B.c[0] * 100; }), im = MKTL.slice(base).map(function (v) { return v / MKTL[base] * 100; });
  var sers = [{ name: A.sym, color: 'var(--sa)', vals: ia }, { name: B.sym, color: 'var(--sb)', vals: ib }, { name: 'Dataset average', color: 'var(--muted)', vals: im, dash: true, w: 1.2 }];
  $('lgIdx').innerHTML = legendHtml(sers);
  drawLine($('cIdx'), { x: x, series: sers, h: 280, yFmt: function (v) { return v; }, refs: [100], tipFmt: function (v) { return nf(v, 1); } });
  // candles
  drawCandles();
  // rolling
  var w = st.rollWin, rx = DATES.slice(base + 1);
  var va = rollStd(R[A.sym], w).slice(base).map(function (v) { return v * Math.sqrt(K) * 100; }), vb = rollStd(R[B.sym], w).slice(base).map(function (v) { return v * Math.sqrt(K) * 100; });
  var vs = [{ name: A.sym, color: 'var(--sa)', vals: va }, { name: B.sym, color: 'var(--sb)', vals: vb }];
  $('lgVol').innerHTML = legendHtml(vs);
  drawLine($('cVol'), { x: rx, series: vs, h: 240, yFmt: function (v) { return v + '%'; }, tipFmt: function (v) { return nf(v, 1) + '%'; }, yMin: 0 });
  var rc = rollCorr(R[A.sym], R[B.sym], w).slice(base);
  drawLine($('cCorr'), { x: rx, series: [{ name: 'Correlation', color: 'var(--fg)', vals: rc }], h: 240, yMin: -1, yMax: 1, refs: [0], yFmt: function (v) { return v.toFixed(1); }, tipFmt: function (v) { return nf(v, 2); } });
  // histograms
  drawHist($('cHistA'), A, 'var(--sa)', M); drawHist($('cHistB'), B, 'var(--sb)', M);
  $('hA').textContent = A.sym; $('hB').textContent = B.sym;
  // technical
  drawTech();
}
function winStartM(code) { var months = code === '3M' ? 3 : code === '6M' ? 6 : code === '1Y' ? 12 : null; if (months == null) return CUR.base; var i = cutoffIdx(months); return Math.max(CUR.base, i < 0 ? 0 : i); }

function drawCandles() {
  var M = CUR, X0 = M[st.cStock.toUpperCase()], S = X0.S, i0 = winStartM(st.cWin), el = $('cCandle');
  var W = Math.max(280, el.clientWidth), Hp = 270, Hv = 70, gap = 18, H = Hp + gap + Hv + 24, m = { l: 56, r: 10, t: 8 };
  var n = N - i0, pw = W - m.l - m.r, lo = Infinity, hi = 0, vmax = 0;
  for (var i = i0; i < N; i++) { if (S.l[i] < lo) lo = S.l[i]; if (S.h[i] > hi) hi = S.h[i]; if (S.v[i] > vmax) vmax = S.v[i]; }
  var dom = niceDomain(lo, hi, 5), ph = Hp - m.t;
  var cx = function (k) { return m.l + (k + 0.5) / n * pw; }, Y = function (v) { return m.t + ph - (v - dom.min) / (dom.max - dom.min) * ph; };
  var bw = Math.max(1, Math.min(10, pw / n * 0.7)), s = '';
  dom.ticks.forEach(function (t) { var y = Y(t); s += '<line class="gr" x1="' + m.l + '" x2="' + (W - m.r) + '" y1="' + y.toFixed(1) + '" y2="' + y.toFixed(1) + '"/><text class="tx" x="' + (m.l - 6) + '" y="' + (y + 4).toFixed(1) + '" text-anchor="end">' + nf(t, 0) + '</text>'; });
  var vy0 = Hp + gap + Hv;
  for (var k = 0; k < n; k++) {
    var j = i0 + k, up = S.c[j] >= S.o[j], col = up ? 'var(--up)' : 'var(--down)', x = cx(k), yo = Y(S.o[j]), yc = Y(S.c[j]);
    s += '<line x1="' + x.toFixed(1) + '" x2="' + x.toFixed(1) + '" y1="' + Y(S.h[j]).toFixed(1) + '" y2="' + Y(S.l[j]).toFixed(1) + '" style="stroke:' + col + ';stroke-width:1"/>';
    s += '<rect x="' + (x - bw / 2).toFixed(1) + '" y="' + Math.min(yo, yc).toFixed(1) + '" width="' + bw.toFixed(1) + '" height="' + Math.max(1, Math.abs(yo - yc)).toFixed(1) + '" style="fill:' + col + '"/>';
    var vh = S.v[j] / vmax * Hv; s += '<rect x="' + (x - bw / 2).toFixed(1) + '" y="' + (vy0 - vh).toFixed(1) + '" width="' + bw.toFixed(1) + '" height="' + vh.toFixed(1) + '" style="fill:' + col + ';opacity:.45"/>';
  }
  s += '<text class="tx" x="' + (m.l - 6) + '" y="' + (Hp + gap + 8) + '" text-anchor="end">' + nf(vmax / 1e5, 0) + 'L</text><text class="tx" x="' + (m.l - 6) + '" y="' + vy0 + '" text-anchor="end">0</text>';
  s += '<g transform="translate(0,' + (H - 6) + ')">' + xTicks(DATES.slice(i0), n, pw, m.l) + '</g>';
  s += '<line class="cross" style="display:none" y1="' + m.t + '" y2="' + vy0 + '"/><rect x="' + m.l + '" y="' + m.t + '" width="' + pw + '" height="' + (vy0 - m.t) + '" fill="transparent"/>';
  var svg = mountSvg(el, W, H, s), cross = svg.querySelector('.cross'), rect = svg.querySelector('rect:last-of-type');
  rect.addEventListener('pointermove', function (e) {
    var b = svg.getBoundingClientRect(), px = (e.clientX - b.left) * (W / b.width), k2 = Math.max(0, Math.min(n - 1, Math.floor((px - m.l) / pw * n))), j = i0 + k2;
    cross.setAttribute('x1', cx(k2)); cross.setAttribute('x2', cx(k2)); cross.style.display = '';
    showTip(el, '<b>' + fdate(DATES[j]) + '</b><br>Open ' + nf(S.o[j]) + '<br>High ' + nf(S.h[j]) + '<br>Low ' + nf(S.l[j]) + '<br>Close ' + nf(S.c[j]) + '<br>Volume ' + nf(S.v[j], 0), cx(k2) * (b.width / W), e.clientY - b.top, b.width);
  });
  rect.addEventListener('pointerleave', function () { cross.style.display = 'none'; hideTip(el); });
}

function drawHist(el, X, color, M) {
  var all = M.A.r.concat(M.B.r), bwid = 0.005, lo = Math.floor(Math.min.apply(null, all) / bwid) * bwid, hi = Math.ceil(Math.max.apply(null, all) / bwid) * bwid;
  var nb = Math.round((hi - lo) / bwid), cnt = function (r) { var c = new Array(nb).fill(0); r.forEach(function (v) { var i = Math.min(nb - 1, Math.floor((v - lo) / bwid + 1e-9)); c[i]++; }); return c; };
  var ca = cnt(M.A.r), cb = cnt(M.B.r), cm = Math.max(Math.max.apply(null, ca), Math.max.apply(null, cb)), mine = X.k === 'a' ? ca : cb;
  var W = Math.max(260, el.clientWidth), H = 220, m = { l: 40, r: 10, t: 8, b: 28 }, pw = W - m.l - m.r, ph = H - m.t - m.b;
  var dy = niceDomain(0, cm, 4); dy.min = 0;
  var Xs = function (v) { return m.l + (v - lo) / (hi - lo) * pw; }, Y = function (v) { return m.t + ph - v / dy.max * ph; }, s = '';
  dy.ticks.forEach(function (t) { var y = Y(t); s += '<line class="gr" x1="' + m.l + '" x2="' + (W - m.r) + '" y1="' + y.toFixed(1) + '" y2="' + y.toFixed(1) + '"/><text class="tx" x="' + (m.l - 6) + '" y="' + (y + 4).toFixed(1) + '" text-anchor="end">' + t + '</text>'; });
  var bw = pw / nb;
  mine.forEach(function (c, i) { if (!c) return; s += '<rect x="' + (m.l + i * bw + 0.5).toFixed(1) + '" y="' + Y(c).toFixed(1) + '" width="' + Math.max(1, bw - 1).toFixed(1) + '" height="' + (m.t + ph - Y(c)).toFixed(1) + '" style="fill:' + color + '"/>'; });
  var tk = niceDomain(lo * 100, hi * 100, 5);
  tk.ticks.forEach(function (t) { var x = Xs(t / 100); if (x < m.l - 1 || x > W - m.r + 1) return; s += '<text class="tx" x="' + x.toFixed(1) + '" y="' + (H - 8) + '" text-anchor="middle">' + t + '%</text>'; });
  var mu = mean(X.r); s += '<line x1="' + Xs(mu).toFixed(1) + '" x2="' + Xs(mu).toFixed(1) + '" y1="' + m.t + '" y2="' + (m.t + ph) + '" style="stroke:var(--fg);stroke-width:1.5;stroke-dasharray:4 3"/>';
  s += '<line class="ax" x1="' + m.l + '" x2="' + (W - m.r) + '" y1="' + (m.t + ph) + '" y2="' + (m.t + ph) + '"/><rect x="' + m.l + '" y="' + m.t + '" width="' + pw + '" height="' + ph + '" fill="transparent"/>';
  var svg = mountSvg(el, W, H, s), rect = svg.querySelector('rect:last-of-type');
  rect.addEventListener('pointermove', function (e) {
    var b = svg.getBoundingClientRect(), px = (e.clientX - b.left) * (W / b.width), i = Math.max(0, Math.min(nb - 1, Math.floor((px - m.l) / bw)));
    showTip(el, '<b>' + ((lo + i * bwid) * 100).toFixed(1) + '% to ' + ((lo + (i + 1) * bwid) * 100).toFixed(1) + '%</b><br>' + mine[i] + ' days (' + (mine[i] / X.r.length * 100).toFixed(1) + '%)', (m.l + (i + 0.5) * bw) * (b.width / W), e.clientY - b.top, b.width);
  });
  rect.addEventListener('pointerleave', function () { hideTip(el); });
  var mo = moments(X.r), best = Math.max.apply(null, X.r), worst = Math.min.apply(null, X.r);
  $(X.k === 'a' ? 'hAstat' : 'hBstat').textContent = 'Dashed line: mean daily return ' + pc(mu, 3) + '. Best day ' + pc(best, 2, true) + ', worst day ' + pc(worst, 2, true) + ', skewness ' + nf(mo.skew, 2) + ', excess kurtosis ' + nf(mo.kurt, 2) + '. Bars are 0.5% wide; both charts share one scale.';
}

function drawTech() {
  var M = CUR, X0 = M[st.tStock.toUpperCase()], c = X0.S.c, base = M.base, x = DATES.slice(base);
  var s50 = sma(c, 50).slice(base), s200 = sma(c, 200).slice(base), px = c.slice(base);
  var ps = [{ name: X0.sym + ' close', color: 'var(--fg)', vals: px, w: 1.4 }, { name: '50-day average', color: 'var(--sa)', vals: s50 }, { name: '200-day average', color: 'var(--sb)', vals: s200 }];
  $('lgTech').innerHTML = legendHtml(ps);
  drawLine($('cTechP'), { x: x, series: ps, h: 260, ml: 56, yFmt: function (v) { return nf(v, 0); }, tipFmt: function (v) { return nf(v, 2); } });
  drawLine($('cRSI'), { x: x, series: [{ name: 'RSI', color: 'var(--fg)', vals: rsi(c, 14).slice(base) }], h: 150, yMin: 0, yMax: 100, refs: [30, 70], yFmt: function (v) { return v; }, tipFmt: function (v) { return nf(v, 1); } });
  var mc = macd(c);
  drawLine($('cMACD'), { x: x, series: [{ name: 'MACD', color: 'var(--sa)', vals: mc.line.slice(base) }, { name: 'Signal', color: 'var(--sb)', vals: mc.sig.slice(base) }], bars: { name: 'Histogram', color: 'var(--muted)', vals: mc.hist.slice(base) }, h: 170, ml: 56, refs: [0], yFmt: function (v) { return nf(v, 1); }, tipFmt: function (v) { return nf(v, 2); } });
}

/* ---------- notes ---------- */
function renderNotes() {
  var miss = D.universe.filter(function (u) { return !u.hasData; }).map(function (u) { return u.symbol; });
  var items = [
    'Source: ' + D.source + '. ' + N + ' trading days, ' + fdate(DATES[0]) + ' to ' + fdate(DATES[N - 1]) + '. Prices run to the close of ' + fdate(DATES[N - 1]) + '. There is no live feed.',
    miss.length ? 'Coverage: ' + D.nStocks + ' of the 50 stocks have price data. No price files were supplied for ' + miss.join(', ') + ', so they are listed but cannot be selected.' : 'Coverage: all 50 stocks in the working universe have price data for the full period.',
    'Excluded: WIPRO appeared in the supplied files but is not in the 50-stock universe, so it is not offered.',
    'Not supplied: NIFTY 50 index prices and company financials. The benchmark comparison and beta use the equal-weighted average of the ' + D.nStocks + ' supplied stocks, and the fundamentals section calculates ratios only from inputs that are loaded.',
    'Returns are simple daily price returns on adjusted closes, without dividends. Efficient frontier weights run from 0% to 100% in each stock, with no short selling and no risk-free asset.',
    'The sector labels follow the constituent snapshot dated 17 November 2026 given in the project brief. The final stock list still needs checking against the official NSE constituent file.'
  ];
  $('noteList').innerHTML = items.map(function (t) { return '<li>' + esc(t) + '</li>'; }).join('');
  var rows = []; Object.keys(D.stocks).forEach(function (s) { D.stocks[s].actions.forEach(function (a) { rows.push('<tr><td><b>' + esc(s) + '</b></td><td>' + fdate(a.date) + '</td><td>' + esc(a.note) + '</td></tr>'); }); });
  $('tAdj').innerHTML = '<thead><tr><th>Ticker</th><th>Effective</th><th>Adjustment</th></tr></thead><tbody>' + rows.join('') + '</tbody><caption class="hint" style="caption-side:bottom;text-align:left;padding-top:6px">The supplied files did not carry adjusted prices. Each factor was inferred from the one-day price drop, the jump in traded volume and the opening gap, and then checked against published news reports of the corporate action. Cash dividends are not adjusted.</caption>';
}

/* ---------- export ---------- */
function csvCell(v) { v = String(v); return /[",\n]/.test(v) ? '"' + v.replace(/"/g, '""') + '"' : v; }
function buildCsv() {
  var M = CUR, L = [];
  function row() { L.push(Array.prototype.slice.call(arguments).map(csvCell).join(',')); }
  row('NSE Efficient Frontier results'); row('Data as of', DATES[N - 1]); row('Source', D.source); row('Period', st.period, 'from', DATES[M.base]); row('Stock A', M.A.sym, M.A.meta.name); row('Stock B', M.B.sym, M.B.meta.name); row();
  row('Measure', M.A.sym, M.B.sym);
  row('Annualised expected return', M.A.mu, M.B.mu); row('Annualised standard deviation', M.A.sig, M.B.sig); row('Maximum drawdown', M.A.mdd, M.B.mdd); row('Beta vs dataset average', M.A.beta, M.B.beta);
  row('Last close', M.A.S.last.close, M.B.S.last.close); row('Period price return', M.A.total, M.B.total); row();
  row('Covariance (annualised)', M.cv); row('Correlation', M.corr); row(); row('Portfolio', 'Weight ' + M.A.sym, 'Weight ' + M.B.sym, 'Expected return', 'Volatility', 'Amount ' + M.A.sym + ' (INR)', 'Amount ' + M.B.sym + ' (INR)');
  var amt = +st.amount > 0 ? +st.amount : 0;
  M.cols.forEach(function (c) { row(c.n, c.p.w, 1 - c.p.w, c.p.mu, c.p.sd, amt * c.p.w, amt * (1 - c.p.w)); });
  row(); row('Efficient frontier points'); row('Weight ' + M.A.sym, 'Expected return', 'Volatility', 'Efficient');
  M.pts.forEach(function (p) { row(p.w, p.mu, p.sd, p.eff ? 'yes' : 'no'); });
  return L.join('\n') + '\n';
}
function buildSummary() {
  var M = CUR, sel = M.sel, amt = +st.amount > 0 ? +st.amount : 0;
  return ['NSE Efficient Frontier: ' + M.A.sym + ' and ' + M.B.sym, 'Data to ' + fdate(DATES[N - 1]) + ', period ' + st.period + ', ' + M.nObs + ' daily returns.',
    M.A.sym + ': return ' + pc(M.A.mu) + ', volatility ' + pc(M.A.sig) + ', max drawdown ' + pc(M.A.mdd),
    M.B.sym + ': return ' + pc(M.B.mu) + ', volatility ' + pc(M.B.sig) + ', max drawdown ' + pc(M.B.mdd),
    'Correlation ' + nf(M.corr, 3) + ', covariance ' + nf(M.cv, 4),
    'Minimum variance: ' + pc(M.wm, 1) + ' ' + M.A.sym + ' / ' + pc(1 - M.wm, 1) + ' ' + M.B.sym + ', volatility ' + pc(M.mvp.sd) + ', return ' + pc(M.mvp.mu),
    'Selected: ' + pc(sel.w, 0) + ' ' + M.A.sym + ' / ' + pc(1 - sel.w, 0) + ' ' + M.B.sym + ', return ' + pc(sel.mu) + ', volatility ' + pc(sel.sd) + (amt ? ', ' + inr(amt * sel.w, 0) + ' / ' + inr(amt * (1 - sel.w), 0) : '')].join('\n');
}
function status(t) { $('expStatus').textContent = t; }
async function saveFile(name, text, mime) {
  try {
    var dl = window.claude && window.claude.use ? await window.claude.use('downloads') : null;
    if (dl) { await dl.save({ filename: name, data: text }); status('Saved ' + name + '.'); return; }
  } catch (e) { if (e && e.code === 'declined') { status('Download cancelled.'); return; } status('The download could not be completed in this view.'); return; }
  var a = document.createElement('a'); a.href = URL.createObjectURL(new Blob([text], { type: mime })); a.download = name; document.body.appendChild(a); a.click(); a.remove(); status('Downloaded ' + name + '.');
}
async function copySummary() {
  var t = buildSummary(), ta = $('copyArea');
  try { await navigator.clipboard.writeText(t); ta.hidden = true; status('Summary copied.'); }
  catch (e) { ta.hidden = false; ta.value = t; ta.focus(); ta.select(); status('Copying was blocked here. The summary is selected below, press Ctrl+C or Cmd+C.'); }
}

/* ---------- wiring ---------- */
function wire() {
  var sec = $('sector'); sec.innerHTML = '<option value="All">All sectors</option>' + D.sectors.map(function (s) { return '<option>' + esc(s) + '</option>'; }).join('');
  $('stocks').addEventListener('click', function (e) {
    var b = e.target.closest('button[data-act]'); if (!b) return; var sym = b.dataset.sym;
    if (b.dataset.act === 'rm') { if (st.a === sym) st.a = null; else if (st.b === sym) st.b = null; }
    else { if (sym === st.a || sym === st.b) return; if (!st.a) st.a = sym; else if (!st.b) st.b = sym; else return; }
    if (st.a === null && st.b) { st.a = st.b; st.b = null; }
    syncPickers(); renderAll();
  });
  $('rmA').onclick = function () { st.a = null; if (st.b) { st.a = st.b; st.b = null; } syncPickers(); renderAll(); };
  $('rmB').onclick = function () { st.b = null; syncPickers(); renderAll(); };
  $('q').oninput = function () { st.q = this.value; renderList(); };
  sec.onchange = function () { st.sector = this.value; renderList(); };
  $('period').onchange = function () { st.period = this.value; renderAll(); };
  $('wA').oninput = function () { st.wA = +this.value; renderPortfolio(); };
  $('tRisk').oninput = function () { st.tRisk = this.value; renderPortfolio(); };
  $('tRet').oninput = function () { st.tRet = this.value; renderPortfolio(); };
  $('amount').oninput = function () { st.amount = this.value; renderPortfolio(); };
  $('cStock').onchange = function () { st.cStock = this.value; drawCandles(); };
  $('cWin').onchange = function () { st.cWin = this.value; drawCandles(); };
  $('rollWin').onchange = function () { st.rollWin = +this.value; renderCharts(); };
  $('tStock').onchange = function () { st.tStock = this.value; drawTech(); };
  $('btnCsv').onclick = function () { saveFile('efficient-frontier-' + CUR.A.sym + '-' + CUR.B.sym + '.csv', buildCsv(), 'text/csv'); };
  $('btnCopy').onclick = copySummary;
  var t; window.addEventListener('resize', function () { clearTimeout(t); t = setTimeout(function () { if (CUR) { renderPortfolio(); renderCharts(); } }, 150); });
}
function syncPickers() {
  ['cStock', 'tStock'].forEach(function (id) {
    var el = $(id), v = el.value || 'a';
    el.innerHTML = '<option value="a">Stock A' + (st.a ? ': ' + esc(st.a) : '') + '</option><option value="b">Stock B' + (st.b ? ': ' + esc(st.b) : '') + '</option>'; el.value = v;
  });
}

function start() {
  fetch('data.json').then(function (r) { if (!r.ok) throw new Error('HTTP ' + r.status); return r.json(); }).then(function (d) {
    D = d; prep();
    $('meta').textContent = 'Source: NSE daily EQ-series prices supplied for this project. Latest trading day in the data: ' + fdate(DATES[N - 1]) + '. ' + D.nStocks + ' stocks, ' + N + ' trading days from ' + fdate(DATES[0]) + '.';
    $('loadmsg').hidden = true; $('main').hidden = false;
    wire(); syncPickers(); renderNotes(); renderAll();
  }, function (e) {
    $('loadmsg').innerHTML = 'The price data file (data.json) could not be loaded: ' + esc(e.message) + '. If you opened index.html directly from disk, serve the folder over HTTP instead, for example with <code>python3 -m http.server</code>.';
  });
}
start();
})();
