import { coordinate, fieldReading, THOUSAND_FIELD } from "./math/field.ts";

export type FieldStage = 1 | 2 | 3;

/** Drawing coordinates use square roots; membership and printed groups use integers. */
export function renderFieldRuler(n: number, stage: FieldStage): string {
  const scale = stage === 3 ? "root" : "number";
  const at = (value: number) => (coordinate(value, scale) * 100).toFixed(5);
  const lo = at(THOUSAND_FIELD.lower);
  const hi = at(THOUSAND_FIELD.upper);
  const dots = stage === 1 ? [997] : Array.from({ length: 66 }, (_, i) => 968 + i);
  const description = stage === 1
    ? "997 is three below the landmark 1000."
    : `The field contains the 64 integers from 969 through 1032. ${n} is selected. ${stage === 3 ? "On the square-root ruler, the two continuous boundaries stand exactly one unit apart." : "968 and 1033 are outside the field."}`;
  return `<div class="field-ruler ${stage === 3 ? "field-ruler-root" : ""}" role="img" aria-label="${description}">
    <div class="field-ruler-caption">${stage === 1 ? "The fraction we know" : stage === 2 ? "One dot for each denominator" : "The same dots, measured by their square roots"}</div>
    <div class="field-ruler-track">
      ${stage > 1 ? `<span class="field-band" style="left:${lo}%;width:${Number(hi) - Number(lo)}%"></span><span class="field-boundary" style="left:${lo}%"></span><span class="field-boundary" style="left:${hi}%"></span>` : ""}
      <span class="field-landmark" style="left:${at(1000)}%"></span>
      ${dots.map(d => `<span class="field-dot ${d < 1000 ? "field-below" : d > 1000 ? "field-above" : "field-exact"} ${fieldReading(d).inField ? "" : "field-outside"} ${d === n ? "field-selected" : ""}" style="left:${at(d)}%"></span>`).join("")}
      <span class="field-selection-label" style="left:clamp(20px,${at(n)}%,calc(100% - 20px))">${n}</span>
    </div>
    <div class="field-axis-labels" style="--landmark:${at(1000)}%"><span>${stage === 3 ? "√968" : "968"}</span><span>${stage === 3 ? "√1000" : "1000"}<small>landmark</small></span><span>${stage === 3 ? "√1033" : "1033"}</span></div>
    ${stage === 3 ? `<div class="field-root-measure"><div><span>31.126729…</span><strong>exactly 1 apart</strong><span>32.126729…</span></div><div class="field-width-bracket" style="margin-left:calc(8px + (100% - 16px) * ${Number(lo) / 100});margin-right:calc(8px + (100% - 16px) * ${(100 - Number(hi)) / 100})" aria-hidden="true"></div><p>The boundaries of the strip. Filled dots sit strictly inside; hollow dots are outside.</p></div>` : stage === 2 ? `<p class="field-ruler-note">969 through 1032: <strong>64 denominators</strong>. The hollow end dots are outside.</p>` : `<p class="field-ruler-note">1000 − 997 = <strong>3</strong>. That is where the tripling comes from.</p>`}
  </div>`;
}

export function renderFieldReading(n: number): string {
  const r = fieldReading(n);
  const magnitude = Math.abs(r.ratio);
  const terms = r.signedTerms.slice(0, 4).map(String).join(", ");
  const motion = n < 1000 ? `Each term is multiplied by ${magnitude}.`
    : n === 1000 ? "The gap is zero, so the expansion ends after 001."
    : `The series alternates: multiply each term by −${magnitude}. Borrowing turns the opening 001 | −${String(magnitude).padStart(3, "0")} into 000 | ${String(r.expectedSecond).padStart(3, "0")}, before any later carry.`;
  const verdict = r.inField
    ? n === 1000 ? "At the landmark: the first box is 001 and every later box is 000."
      : n < 1000 ? `The first two boxes keep the pattern: 001, then ${r.groups[1]}.`
        : `After borrowing, the first two boxes are 000, then ${r.groups[1]}.`
    : `Already at the second box, ${String(r.expectedSecond).padStart(3, "0")} becomes ${r.groups[1]}. This denominator is outside the field.`;
  return `<div class="field-reading-header"><h4>1/${n}</h4><span class="field-membership ${r.inField ? "" : "field-membership-out"}">${r.inField ? "Inside the field" : "Outside the field"}</span></div>
    <p class="field-series-terms">Before carrying: <strong>${terms}, …</strong></p><p class="field-motion">${motion}</p>
    <div class="field-groups" aria-label="First six actual base-1000 groups: ${r.groups.join(", ")}">${r.groups.map((g, i) => `<span${i === 1 && !r.inField ? ' class="field-changed"' : ""}>${g}</span>`).join("")}</div>
    <p class="field-verdict">${verdict}</p>
    <p class="field-check">Square the gap: <strong>${magnitude}² = ${magnitude * magnitude} ${r.inField ? "&lt;" : "&gt;"} ${n}</strong>.</p>`;
}
