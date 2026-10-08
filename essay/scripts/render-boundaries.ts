import { REPETITION_BOUNDARIES } from "../src/repetition-boundaries.ts";

const atlas = "https://github.com/mikedotexe/reptends/blob/main/docs/PROOF_STATUS_ATLAS.md";
const power = (base: bigint, exponent: number) => `${base}<sup>${exponent}</sup>`;

/** Exact examples are baked into the artifact, including the no-JavaScript view. */
export function renderRepetitionBoundaries(): string {
  const example = REPETITION_BOUNDARIES.find(item => item.denominator === 997n)!;
  const { firstChangedIndex, firstChangedRow, decimalEnd, groupedEnd } = example;
  const rows = REPETITION_BOUNDARIES.map(item => {
    const end = item.decimalEnd;
    const split = end.followingPart
      ? `${end.endingPart}<span class="boundary-divider" aria-hidden="true">│</span><span class="boundary-next">${end.followingPart}</span>`
      : `${end.endingPart}<span class="boundary-divider" aria-hidden="true">│</span>`;
    return `<tr data-boundary-denominator="${item.denominator}">
      <th scope="row">1/${item.denominator}<small>${item.width}-digit words · ×${item.multiplier}</small></th>
      <td>${item.decimal.period} repeating digits<small>${item.decimal.preperiod ? "after one initial nonrepeating 0" : "starting at the decimal point"}</small></td>
      <td>${power(item.multiplier, end.wordIndex)}<small>${end.coefficientCount} power positions, including 1</small></td>
      <td><span class="boundary-word" aria-label="${end.endingPart} ends the first repetition${end.followingPart ? `; ${end.followingPart} begins the next` : "; the word also ends here"}">${split}</span></td>
      <td>${item.grouped.period} repeating words<small>${item.grouped.preperiod ? "+ 1 startup word; " : ""}through ${power(item.multiplier, item.groupedEnd.wordIndex)}</small></td>
    </tr>`;
  }).join("\n");

  const receipts = REPETITION_BOUNDARIES.map(item => {
    const end = item.decimalEnd;
    const group = item.groupedEnd;
    const lastDigit = item.decimal.rows.at(-1)!.word;
    return `<div class="boundary-receipt"><h4>1/${item.denominator}</h4>
      <p>Digit ${end.position}: 10 × ${end.remainderBefore} = ${item.denominator} × ${lastDigit} + ${end.remainderAfter}. Remainder ${end.remainderAfter} returns to the start of the decimal loop${item.decimal.preperiod ? ", after the initial zero" : ""}.</p>
      <p>Group ${group.coefficientCount}: ${item.base} × ${group.remainderBefore} = ${item.denominator} × ${group.wordText} + ${group.remainderAfter}. Remainder ${group.remainderAfter} returns to the start of the word loop${item.grouped.preperiod ? ", after the startup word" : ""}.</p>
      <p>Power at the first decimal endpoint:<br><span class="boundary-integer">${power(item.multiplier, end.wordIndex)} = ${end.power}</span></p>
      ${group.wordIndex !== end.wordIndex ? `<p>Power at the aligned word endpoint:<br><span class="boundary-integer">${power(item.multiplier, group.wordIndex)} = ${group.power}</span></p>` : ""}
    </div>`;
  }).join("\n");

  return `<article id="soft-end" class="boundary-card" aria-labelledby="soft-end-title">
    <p class="small-label">A FINITE DESCRIPTION OF AN INFINITE DECIMAL</p>
    <h3 id="soft-end-title">When have we seen enough?</h3>
    <p class="boundary-intro">Once a long-division remainder returns, every later digit is determined. That is a useful “soft end”: we have enough information to describe the rest. For 1/997, three different moments matter.</p>
    <ol class="boundary-landmarks">
      <li><span class="small-label">01 / THE FIRST CARRY</span><h4>Group ${firstChangedIndex + 1}</h4>
        <p class="boundary-power">${power(3n, firstChangedIndex)} = ${firstChangedRow.raw}</p>
        <p>The decimal prints <strong>${firstChangedRow.word}</strong>. The clean visible prefix ends, while the powers keep growing.</p>
        <button class="button small enhancement" type="button" data-boundary-position="${firstChangedIndex}">Inspect the first carry</button>
      </li>
      <li><span class="small-label">02 / THE DECIMAL RETURNS</span><h4>Digit ${decimalEnd.position}</h4>
        <p class="boundary-power">${power(3n, decimalEnd.wordIndex)} · group ${decimalEnd.coefficientCount}</p>
        <p>The first <strong>166-digit repetend</strong> is complete. Its last digit falls inside this word.</p>
        <div class="boundary-split" aria-label="Word 700: 7 ends the first repetend; 00 starts its next copy"><span><strong>7</strong><small>last digit</small></span><b aria-hidden="true">│</b><span class="boundary-next"><strong>00</strong><small>next copy</small></span></div>
        <button class="button small enhancement" type="button" data-boundary-position="${decimalEnd.wordIndex}">Inspect the decimal return</button>
      </li>
      <li><span class="small-label">03 / THE WORDS ALIGN AGAIN</span><h4>Group ${groupedEnd.coefficientCount}</h4>
        <p class="boundary-power">${power(3n, groupedEnd.wordIndex)} · digit ${groupedEnd.coefficientCount * example.width}</p>
        <p>The word <strong>${groupedEnd.wordText}</strong> closes the grouped loop. These 498 places hold <strong>three copies</strong> of the decimal repetend.</p>
        <button class="button small enhancement" type="button" data-boundary-position="${groupedEnd.wordIndex}">Inspect the word return</button>
      </li>
    </ol>
    <p id="boundary-position" class="boundary-position enhancement">Shared position: group 7, the first carry.</p>
    <p class="boundary-caveat">Count powers from 3<sup>0</sup> = 1: there are <strong>56 power positions</strong> through the word containing the first decimal endpoint, or <strong>166</strong> through the aligned word endpoint. A power labels a position; its printed word also includes carries from later terms. Stopping the raw sum there would still leave a tail.</p>
    <details id="boundary-comparison" class="math-note"><summary>Compare the stopping places for 97, 997, 94, and 994</summary>
      <p>The <a href="${atlas}">proof-status atlas</a> records <code>digit_periodicity</code> as <strong>reproved-here</strong> for coprime prime examples and <code>power_order_formula</code> as <strong>classical</strong>. The four cases below are <strong>computed examples</strong>, checked against ordinary long division, including the startup for the composite denominators.</p>
      <p>For 94 = 100 − 6 and 994 = 1000 − 6, the powers are 1, 6, 36, … . Both decimals have one initial nonrepeating zero. Keep grouping from the decimal point; the startup word counts toward the power position.</p>
      <p class="fine-print">The divider marks the end of the first decimal repetend. Digits to its right start the next copy. On small screens, scroll the table sideways to compare every column.</p>
      <div class="boundary-table-scroll" tabindex="0" role="region" aria-label="Comparison of four repeating decimals; horizontally scrollable">
        <table class="boundary-table"><caption>Which power position contains the last digit?</caption>
          <thead><tr><th scope="col">Reciprocal</th><th scope="col">Decimal loop</th><th scope="col">Associated power</th><th scope="col">Word at boundary</th><th scope="col">Aligned word loop</th></tr></thead>
          <tbody>${rows}</tbody>
        </table>
      </div>
      <p>The cycle length depends on the returning remainders. It does not increase steadily with the denominator or with the gap from a power of ten.</p>
      <details class="math-note boundary-receipts"><summary>Inspect the returning remainders and complete powers</summary>${receipts}</details>
    </details>
  </article>`;
}
