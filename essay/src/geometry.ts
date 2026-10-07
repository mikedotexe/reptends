import { recurrenceTrace } from './math/lifts.ts';
import { enumerateTriplePlane, tripleCoefficient, type OrderedTriple } from './math/triple-contributions.ts';

/**
 * A visual continuation of the original square-reciprocal-diagonals and
 * cubing-a-grid-of-triples sketches (3 September 2026). Arithmetic comes from
 * the preserved research engine; only bounded drawing coordinates use Number.
 */
export function initGeometry(root: HTMLElement): void {
  if (root.dataset.initialized === 'true') return;

  const base = 10000n;
  const square = recurrenceTrace({ base, coefficients: [2n, -1n] }, 7);
  const cube = recurrenceTrace({ base, coefficients: [3n, -3n, 1n] }, 8);
  for (const row of square.rows) {
    if (row.raw !== BigInt(row.index) || row.word !== row.raw) {
      throw new Error('Square coefficients disagree with exact long division.');
    }
  }
  for (const row of cube.rows) {
    if (row.raw !== tripleCoefficient(BigInt(row.index + 1)) || row.word !== row.raw) {
      throw new Error('Cube coefficients disagree with exact long division.');
    }
  }

  root.classList.add('geometry-explorer');
  root.innerHTML = `
    <div class="geometry-topline">
      <div class="geometry-modes" role="group" aria-label="Choose a product">
        <button type="button" data-geometry-mode="square" aria-pressed="true">Square <span aria-hidden="true">²</span></button>
        <button type="button" data-geometry-mode="cube" aria-pressed="false">Cube <span aria-hidden="true">³</span></button>
      </div>
      <span class="geometry-factor" data-geometry="factor">(1/9999)²</span>
    </div>
    <p class="geometry-explanation" data-geometry="explanation"></p>
    <div class="geometry-controls">
      <button type="button" class="geometry-transform" data-geometry-action="transform" aria-pressed="false">Align by place</button>
      <div class="geometry-stepping" role="group" aria-label="Choose a contribution slice">
        <button type="button" data-geometry-action="previous" aria-label="Previous contribution slice">← <span>Previous</span></button>
        <span class="geometry-step" data-geometry="step">4 of 6</span>
        <button type="button" data-geometry-action="next" aria-label="Next contribution slice"><span>Next</span> →</button>
      </div>
    </div>
    <div class="geometry-rotation" data-geometry="rotation" hidden>
      <label for="geometry-angle">Rotate the grid <output for="geometry-angle" data-geometry="angle-label">36°</output></label>
      <input id="geometry-angle" type="range" min="12" max="78" step="1" value="36" aria-label="Rotate the three-dimensional contribution grid">
    </div>
    <svg class="geometry-drawing" role="img" aria-labelledby="geometry-svg-title geometry-svg-description"></svg>
    <div class="geometry-result" aria-live="polite" aria-atomic="true" data-geometry="result"></div>
    <div class="geometry-words-heading"><span>Four-digit groups</span><span>Output place ↓</span></div>
    <div class="geometry-words" data-geometry="words"></div>
    <p class="geometry-footnote" data-geometry="footnote"></p>
    <details class="geometry-math">
      <summary>Show the mathematics</summary>
      <div>
        <p>Write B = 10000. The geometric series gives 1/(B − 1) = B<sup>−1</sup> + B<sup>−2</sup> + ⋯. Pick one term from each factor and multiply. The exponents add, so products with the same exponent belong to the same output place.</p>
        <p>With two factors, the positive pairs i + j = s number s − 1. With three factors, the positive triples i + j + k = s number (s − 1)(s − 2)/2 for s ≥ 3. Order matters: picking position 1 from the first factor and position 2 from the second is a different choice from picking them the other way round.</p>
        <p class="geometry-equation">1/(B − 1)² = ∑<sub>s ≥ 2</sub> (s − 1)/B<sup>s</sup><br>1/(B − 1)³ = ∑<sub>s ≥ 3</sub> ((s − 1)(s − 2)/2)/B<sup>s</sup></p>
        <p>These convergent series collect contributions before carrying. Their coefficients grow without bound, so they cannot stay four-digit groups forever. Every group shown here is independently checked against exact long division; the infinite grid extends beyond the six highlighted slices.</p>
      </div>
    </details>`;

  const get = <T extends Element>(selector: string): T => {
    const element = root.querySelector<T>(selector);
    if (!element) throw new Error(`Missing geometry element: ${selector}`);
    return element;
  };
  const svg = get<SVGSVGElement>('.geometry-drawing');
  const transform = get<HTMLButtonElement>('[data-geometry-action="transform"]');
  const previous = get<HTMLButtonElement>('[data-geometry-action="previous"]');
  const next = get<HTMLButtonElement>('[data-geometry-action="next"]');
  const angle = get<HTMLInputElement>('#geometry-angle');
  const modes = [...root.querySelectorAll<HTMLButtonElement>('[data-geometry-mode]')];
  const result = get<HTMLElement>('[data-geometry="result"]');
  const words = get<HTMLElement>('[data-geometry="words"]');
  const motion = window.matchMedia('(prefers-reduced-motion: reduce)');
  const pairs = Array.from({ length: 6 }, (_, index) => index + 1)
    .flatMap(j => Array.from({ length: 7 - j }, (_, index) => ({ i: index + 1, j, place: index + 1 + j })));
  const triples = Array.from({ length: 6 }, (_, index) => enumerateTriplePlane(index + 3))
    .flatMap(plane => plane.points.map(point => ({ ...point, place: plane.place })));

  let mode: 'square' | 'cube' = 'square';
  let slice = 3;
  let layout = 0;
  let target = 0;
  let busy = false;
  let animation = 0;
  const selectedPlace = (): number => slice + (mode === 'square' ? 2 : 3);
  const ns = 'http://www.w3.org/2000/svg';

  function add(tag: string, attributes: Record<string, string | number> = {}, content = ''): SVGElement {
    const node = document.createElementNS(ns, tag);
    Object.entries(attributes).forEach(([name, value]) => node.setAttribute(name, String(value)));
    if (content) node.textContent = content;
    svg.append(node);
    return node;
  }

  function label(x: number, y: number, content: string, attributes: Record<string, string | number> = {}): SVGElement {
    return add('text', { x, y, ...attributes }, content);
  }

  function drawSquare(width: number, selected: number): void {
    const left = 43;
    const unit = (width - left - 12) / 7;
    const center = (slot: number): number => left + (slot + 0.5) * unit;
    const size = Math.min(32, unit - 5);
    label(width / 2 + 13, 22, layout < 0.5 ? 'Position in the first factor' : 'Output place: i + j', { 'text-anchor': 'middle', class: 'geometry-axis-title' });
    for (let i = 1; i <= 6; i += 1) {
      label(center(i), 48, String(i), { 'text-anchor': 'middle', opacity: 1 - layout });
    }
    for (let place = 1; place <= 7; place += 1) {
      label(center(place - 1), 48, String(place), { 'text-anchor': 'middle', opacity: layout });
    }
    label(12, 176, 'Second factor', { transform: 'rotate(-90 12 176)', 'text-anchor': 'middle', class: 'geometry-axis-title' });
    for (let j = 1; j <= 6; j += 1) label(35, 86 + (j - 1) * 39, String(j), { 'text-anchor': 'end' });
    for (const pair of pairs) {
      const x = center(pair.i + (pair.j - 1) * layout);
      const y = 81 + (pair.j - 1) * 39;
      const active = pair.place === selected;
      const tile = add('rect', {
        x: x - size / 2, y: y - size / 2, width: size, height: size, rx: 3,
        class: active ? 'geometry-tile geometry-tile-active' : 'geometry-tile',
        'data-pair': `${pair.i},${pair.j}`, 'data-active': String(active),
      });
      const title = document.createElementNS(ns, 'title');
      title.textContent = `Positions (${pair.i}, ${pair.j}): one contribution to place ${pair.place}`;
      tile.append(title);
      label(x, y + 4, '1', { 'text-anchor': 'middle', class: active ? 'geometry-unit geometry-unit-active' : 'geometry-unit' });
    }
    if (layout === 1) {
      label(center(0), 86, '0', { 'text-anchor': 'middle', class: 'geometry-empty' });
    }
    label(width / 2, 318, layout === 1 ? 'Same place. Same column. Add.' : 'A diagonal gathers equal weights.', { 'text-anchor': 'middle', class: 'geometry-drawing-caption' });
  }

  function drawCube(width: number, selected: number): void {
    type Vector = readonly [number, number, number];
    const active = enumerateTriplePlane(selected).points;
    const yaw = Number(angle.value) * Math.PI / 180;
    const cy = Math.cos(yaw), sy = Math.sin(yaw), cp = Math.cos(0.43), sp = Math.sin(0.43);
    const camera = (p: Vector) => ({ x: -sy * p[0] + cy * p[1], y: sp * cy * p[0] + sp * sy * p[1] - cp * p[2], depth: cp * cy * p[0] + cp * sy * p[1] + sp * p[2] });
    const origin: Vector = [0, 0, 0];
    const axes: Vector[] = [[5.6, 0, 0], [0, 5.6, 0], [0, 0, 5.6]];
    const bounds = [origin, ...axes].map(camera);
    const extent = (values: number[]): [number, number] => [Math.min(...values), Math.max(...values)];
    const [x0, x1] = extent(bounds.map(p => p.x));
    const [y0, y1] = extent(bounds.map(p => p.y));
    const scale = Math.min((width - 76) / (x1 - x0), 235 / (y1 - y0));
    const project = (p: Vector) => {
      const q = camera(p);
      return { x: width / 2 + (q.x - (x0 + x1) / 2) * scale, y: 165 + (q.y - (y0 + y1) / 2) * scale, depth: q.depth };
    };
    const faceUnit = (p: OrderedTriple) => ({ x: (p.j - p.i) / Math.sqrt(2), y: (p.i + p.j - 2 * p.k) / Math.sqrt(6) });
    const faceBounds = active.map(faceUnit);
    const [fx0, fx1] = extent(faceBounds.map(p => p.x));
    const [fy0, fy1] = extent(faceBounds.map(p => p.y));
    const faceScale = Math.min((width - 92) / Math.max(3, fx1 - fx0), 215 / Math.max(3, fy1 - fy0));
    const faceProject = (p: OrderedTriple) => {
      const q = faceUnit(p);
      return { x: width / 2 + (q.x - (fx0 + fx1) / 2) * faceScale, y: 163 + (q.y - (fy0 + fy1) / 2) * faceScale };
    };
    const position = (p: OrderedTriple) => {
      const a = project([p.i - 1, p.j - 1, p.k - 1]);
      const b = faceProject(p);
      return { x: a.x * (1 - layout) + b.x * layout, y: a.y * (1 - layout) + b.y * layout };
    };
    label(width / 2, 22, layout < 0.5 ? 'Three factors. Three choices: i, j, k.' : 'One slice, seen face-on', { 'text-anchor': 'middle', class: 'geometry-axis-title' });
    if (layout < 1) {
      const vertices: Vector[] = [origin, [5, 0, 0], [0, 5, 0], [0, 0, 5]];
      for (let a = 0; a < vertices.length; a += 1) for (let b = a + 1; b < vertices.length; b += 1) {
        const p = project(vertices[a]!), q = project(vertices[b]!);
        add('line', { x1: p.x, y1: p.y, x2: q.x, y2: q.y, class: 'geometry-wire', opacity: 1 - layout });
      }
      const start = project(origin);
      axes.forEach((axis, index) => {
        const end = project(axis);
        add('line', { x1: start.x, y1: start.y, x2: end.x, y2: end.y, class: 'geometry-axis', opacity: 1 - layout });
        label(end.x, end.y + (index < 2 ? 17 : -10), ['i', 'j', 'k'][index]!, { 'text-anchor': 'middle', opacity: 1 - layout });
      });
      const context = triples.filter(p => p.place !== selected)
        .map(p => ({ p, q: project([p.i - 1, p.j - 1, p.k - 1]) })).sort((a, b) => a.q.depth - b.q.depth);
      context.forEach(({ p, q }) => add('circle', { cx: q.x, cy: q.y, r: 2.6, class: 'geometry-context', opacity: (1 - layout) * 0.42, 'data-context': `${p.i},${p.j},${p.k}` }));
    }
    if (selected > 3) {
      const corners: OrderedTriple[] = [{ i: selected - 2, j: 1, k: 1 }, { i: 1, j: selected - 2, k: 1 }, { i: 1, j: 1, k: selected - 2 }];
      add('polygon', { points: corners.map(p => { const q = position(p); return `${q.x},${q.y}`; }).join(' '), class: 'geometry-slice' });
    }
    for (const p of active) for (const q of active) {
      const delta = [q.i - p.i, q.j - p.j, q.k - p.k];
      if ((q.i > p.i || (q.i === p.i && q.j > p.j)) && delta.reduce((sum, value) => sum + Math.abs(value), 0) === 2) {
        const a = position(p), b = position(q);
        add('line', { x1: a.x, y1: a.y, x2: b.x, y2: b.y, class: 'geometry-slice-line' });
      }
    }
    for (const p of active) {
      const q = position(p);
      const point = add('circle', { cx: q.x, cy: q.y, r: width < 380 ? 8 : 10, class: 'geometry-point', 'data-triple': `${p.i},${p.j},${p.k}` });
      const title = document.createElementNS(ns, 'title');
      title.textContent = `Positions (${p.i}, ${p.j}, ${p.k}): one contribution to place ${selected}`;
      point.append(title);
      label(q.x, q.y + 4, '1', { 'text-anchor': 'middle', class: 'geometry-unit geometry-unit-active' });
    }
    if (layout === 1) {
      for (let count = 1; count <= selected - 2; count += 1) {
        const first = active.find(p => selected - p.k - 1 === count)!;
        label(19, faceProject(first).y + 4, String(count), { 'text-anchor': 'middle', class: 'geometry-row-count', 'data-row-count': count });
      }
    }
    label(width / 2, 318, layout === 1 ? `Rows of 1 through ${selected - 2} make ${tripleCoefficient(BigInt(selected))} choices.` : 'Highlighted choices all have i + j + k = ' + selected + '.', { 'text-anchor': 'middle', class: 'geometry-drawing-caption' });
  }

  function draw(): void {
    const width = Math.max(280, svg.getBoundingClientRect().width || 680);
    const selected = selectedPlace();
    const count = mode === 'square' ? BigInt(selected - 1) : tripleCoefficient(BigInt(selected));
    svg.setAttribute('viewBox', `0 0 ${width} 338`);
    svg.replaceChildren();
    add('title', { id: 'geometry-svg-title' }, `${mode === 'square' ? 'Squaring' : 'Cubing'}: ${count} ordered choices at place ${selected}`);
    add('desc', { id: 'geometry-svg-description' }, mode === 'square'
      ? `Each tile chooses a term from each of two factors. The ${count} highlighted tiles have positions summing to ${selected}; each contributes 1/10000^${selected}. Aligning shifts each row so equal output places share a column. The empty first place retains its zero group. Only the first six complete diagonals are shown.`
      : `Each point chooses a term from each of three factors. The ${count} highlighted points have positions summing to ${selected}; each contributes 1/10000^${selected}. The face-on view displays rows of lengths 1 through ${selected - 2}. The first two places retain zero groups. The first six complete slices, containing 56 points, are shown.`);
    if (mode === 'square') drawSquare(width, selected); else drawCube(width, selected);
    root.dataset.mode = mode;
    root.dataset.place = String(selected);
    root.dataset.count = String(count);
    root.dataset.view = busy ? 'moving' : target === 1 ? (mode === 'square' ? 'aligned' : 'face') : 'grid';
    previous.disabled = busy || slice === 0;
    next.disabled = busy || slice === 5;
    transform.setAttribute('aria-disabled', String(busy));
    transform.setAttribute('aria-pressed', String(target === 1));
    transform.textContent = mode === 'square'
      ? (target === 1 ? 'Show the pairings' : 'Align by place')
      : (target === 1 ? 'Back to the grid' : 'Face the slice');
    angle.disabled = busy || target === 1;
    get<HTMLElement>('[data-geometry="angle-label"]').textContent = `${angle.value}°`;
    modes.forEach(button => { button.disabled = busy; });
  }

  function announce(): void {
    const selected = selectedPlace();
    const count = mode === 'square' ? BigInt(selected - 1) : tripleCoefficient(BigInt(selected));
    get<HTMLElement>('[data-geometry="step"]').textContent = `${slice + 1} of 6`;
    get<HTMLElement>('[data-geometry="factor"]').textContent = mode === 'square' ? '(1/9999)²' : '(1/9999)³';
    get<HTMLElement>('[data-geometry="explanation"]').textContent = mode === 'square'
      ? 'Choose one term from each of two identical lists. Every tile is one ordered pair of choices; each diagonal gathers terms with the same weight.'
      : 'Add a third list. Every point is one ordered triple of choices. A flat slice through the grid gathers equal weights into a triangular count.';
    get<HTMLElement>('[data-geometry="rotation"]').hidden = mode !== 'cube';
    result.innerHTML = `<span class="geometry-count">${count}</span><span>ordered ${mode === 'square' ? 'pairs' : 'triples'} at place <strong>${selected}</strong><small>Each contributes 1/10000<sup>${selected}</sup></small></span>`;
    modes.forEach(button => button.setAttribute('aria-pressed', String(button.dataset.geometryMode === mode)));
    const trace = mode === 'square' ? square : cube;
    words.style.setProperty('--geometry-word-count', String(trace.rows.length));
    words.replaceChildren(...trace.rows.map(row => {
      const slot = document.createElement('span');
      slot.className = `geometry-word${row.index + 1 === selected ? ' geometry-word-selected' : ''}${row.word === 0n ? ' geometry-word-zero' : ''}`;
      slot.setAttribute('aria-label', `Place ${row.index + 1}: ${row.word.toString().padStart(4, '0')}${row.index + 1 === selected ? ', selected' : ''}`);
      slot.innerHTML = `<span>${row.index + 1}</span><strong>${row.word.toString().padStart(4, '0')}</strong>`;
      return slot;
    }));
    get<HTMLElement>('[data-geometry="footnote"]').textContent = mode === 'square'
      ? 'Keep the first 0000: two positive positions cannot add to 1. These seven groups match exact long division. Collecting the contributions comes first; carrying matters further along.'
      : 'Keep both opening 0000 groups: three positive positions cannot add to 1 or 2. These eight groups match exact long division. The triangular counts are contributions before carrying.';
  }

  function finish(): void {
    layout = target;
    busy = false;
    draw();
    announce();
  }

  transform.addEventListener('click', () => {
    if (busy) return;
    const startLayout = layout;
    target = 1 - target;
    if (motion.matches) { finish(); return; }
    busy = true;
    let startTime: number | undefined;
    const frame = (timestamp: number): void => {
      startTime ??= timestamp;
      const progress = Math.min(1, (timestamp - startTime) / 850);
      layout = startLayout + (target - startLayout) * progress * progress * (3 - 2 * progress);
      if (progress === 1 || motion.matches) { finish(); return; }
      draw();
      animation = window.requestAnimationFrame(frame);
    };
    draw();
    animation = window.requestAnimationFrame(frame);
  });
  previous.addEventListener('click', () => { if (!busy && slice > 0) { slice -= 1; draw(); announce(); } });
  next.addEventListener('click', () => { if (!busy && slice < 5) { slice += 1; draw(); announce(); } });
  modes.forEach(button => button.addEventListener('click', () => {
    if (busy || button.dataset.geometryMode === mode) return;
    mode = button.dataset.geometryMode === 'cube' ? 'cube' : 'square';
    layout = 0;
    target = 0;
    announce();
    draw();
  }));
  angle.addEventListener('input', () => { if (!busy && target === 0) draw(); });
  motion.addEventListener('change', () => {
    if (motion.matches && busy) { window.cancelAnimationFrame(animation); finish(); }
  });
  new ResizeObserver(() => draw()).observe(svg);
  announce();
  draw();
  root.dataset.initialized = 'true';
}
