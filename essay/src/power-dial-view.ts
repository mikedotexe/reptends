import { powerFamily, regroup997 } from "./math/power-dial.ts";

const number = (n: number) => n.toLocaleString("en-US");

export function renderPowerFamily(width: number): string {
  const p = powerFamily(width);
  const f = p.field;
  const barWidth = f.ordinaryWidth / 2001 * 100;
  return `<div class="dial-reading-head"><h4 id="power-fraction">1/${p.denominator}</h4><span class="dial-kept">Gap stays 3</span></div>
    <p class="dial-equation">${number(p.base)} − 3 = ${number(p.denominator)}</p>
    <p class="dial-opening"><strong id="power-count">${p.cleanCount}</strong> opening groups keep the powers of three.</p>
    <div class="power-clean-groups" aria-label="The first ${p.cleanCount} unchanged groups">${p.groups.slice(0, p.cleanCount).map(g => `<span>${g}</span>`).join("")}</div>
    <div class="power-prediction">
      <div><span class="dial-label">The next power of three</span><strong id="power-next-expected">${p.expected}</strong><p>What will group ${p.firstChangedPosition} actually print?</p></div>
      <button id="power-reveal" class="button primary enhancement" type="button" aria-expanded="true" aria-controls="power-answer">Check the next group</button>
      <div id="power-answer" class="power-answer">
        <p class="dial-label">The printed group</p><strong id="power-next-actual">${p.actual}</strong>
        <p class="dial-carry-equation">${p.expected} + ${p.carry} = ${p.actual}</p>
        <p>The still-unwritten tail carries <strong>${p.carry}</strong> into this place. Even though ${p.expected} fits in ${width} digits, it receives that extra contribution.</p>
        <p class="dial-tail-check">${number(p.nextPower)} = ${number(p.denominator)} × ${p.carry} + ${number(p.nextPower % p.denominator)}</p>
        <p class="dial-small">The next power, ${number(p.nextPower)}, divided by ${number(p.denominator)} gives the incoming carry ${p.carry}. <a href="#power-dial-proof">Why this accounts for the whole tail.</a></p>
      </div>
    </div>
    <div class="power-field-measure">
      <h4>More neighbours. The same root width.</h4>
      <p><strong id="power-field-count">${f.count}</strong> whole-number members: <span id="power-field-range">${number(f.first)} through ${number(f.last)}</span>.</p>
      <div class="power-measure-row">
        <div class="power-measure-label"><span>Width on the number ruler</span><strong>≈ ${f.ordinaryWidth.toFixed(2)}</strong></div>
        <div class="power-measure-track" role="img" aria-label="Ordinary field width approximately ${f.ordinaryWidth.toFixed(2)}, on a fixed width scale from zero to 2001"><span id="power-number-bar" style="width:${barWidth}%"></span></div>
        <div class="power-measure-scale"><span>0</span><span>2,001 units</span></div>
      </div>
      <div class="power-measure-row power-root-row">
        <div class="power-measure-label"><span>Width on the square-root ruler</span><strong>exactly <span id="power-root-width">1</span></strong></div>
        <div class="power-root-strip" role="img" aria-label="Square-root field width exactly one; the lower and upper boundaries differ by one"></div>
        <div class="power-root-endpoints"><span>≈ <span id="power-root-lower">${f.lowerRoot.toFixed(4)}</span></span><span>≈ <span id="power-root-upper">${f.upperRoot.toFixed(4)}</span></span></div>
      </div>
      <p class="dial-small">The top bar measures width on a fixed 0–2,001 scale. The bottom strip measures one square-root unit. Its boundary labels move as the power grows; their exact difference stays 1. Counts describe integer members, while widths measure the continuous interval.</p>
    </div>`;
}

export function renderRegrouping(width: number): string {
  const p = regroup997(width);
  return `<div class="dial-reading-head"><h4>1/997</h4><span class="dial-kept">Fraction stays fixed</span></div>
    <p id="group-equation" class="dial-equation">${number(p.base)} = 997 × ${p.quotient} + ${p.remainder}</p>
    <div class="group-recipe"><div><span class="dial-label">Start with</span><strong id="group-quotient">${p.quotient}</strong></div><div><span class="dial-label">Then multiply by</span><strong id="group-remainder">${p.remainder}</strong></div><div><span class="dial-label">Unchanged opening groups</span><strong id="group-clean-count">${p.cleanCount}</strong></div></div>
    <p class="group-coefficients">Before carrying: <strong>${p.coefficients.slice(0, Math.min(4, p.coefficients.length)).join(", ")}, …</strong></p>
    <p class="dial-label group-tape-label">The same first 60 decimal digits, in ${width}-digit boxes</p>
    <div id="group-tape" class="group-tape" aria-label="First sixty decimal digits of one over 997, grouped in ${width}s">${p.tapeGroups.map((g, i) => `<span class="group-digit-word"${i < p.cleanCount ? ' data-clean="true"' : ""}${i === p.cleanCount ? ' data-change="first"' : ""}>${g}</span>`).join("")}</div>
    <div class="group-tape-key"><span><i class="group-key-clean" aria-hidden="true"></i>Unchanged opening</span><span><i class="group-key-change" aria-hidden="true"></i>First carried group</span></div>
    <p class="group-change">At group ${p.firstChangedPosition}, <strong id="group-next-expected">${p.expected}</strong> receives ${p.carry}, printing <strong id="group-next-actual">${p.actual}</strong>.</p>
    <p class="dial-small">The decimal digits and their value stay the same. The boundaries between boxes move, so the starting coefficient and multiplier change. Six-digit boxes pair the original three-digit boxes: 001 | 003 becomes 001003.</p>`;
}
