import {
  OPENING_EXAMPLES,
  OPENING_GROUP_COUNT,
  POWER_STACK,
  POWER_STACK_RESULT,
  STACK_FIRST_GROUP,
  STACK_LAST_GROUP,
} from "../src/opening-examples.ts";
import { formatWord } from "../src/math/lifts.ts";

/** Render exact curated examples at build time so they are visible without JS. */
export function renderOpeningExamples(): string {
  return OPENING_EXAMPLES.map(example => {
    const { denominator, base, width, rows, firstChangedIndex } = example;
    const first = rows[firstChangedIndex]!;
    const groups = rows.map((row, index) => {
      const kind = index < firstChangedIndex ? "pattern" : index === firstChangedIndex ? "change" : "later";
      const digits = formatWord(row.word, base);
      return '<span class="decimal-group decimal-' + kind + '" data-kind="' + kind + '" data-word="' + digits + '">' + digits + '</span><wbr>';
    }).join("");
    const lastClean = rows[firstChangedIndex - 1]!;
    return '<article class="decimal-example" data-denominator="' + denominator + '" data-width="' + width + '">'
      + '<div class="decimal-example-heading"><h3>1/' + denominator + '</h3>'
      + '<span>' + denominator + ' = ' + base + ' − 3</span><span class="decimal-width">' + width + '-digit groups</span></div>'
      + '<p class="decimal-expansion" aria-label="The first ' + (OPENING_GROUP_COUNT * width) + ' decimal digits of one over ' + denominator + '"><span class="decimal-point">0.</span>' + groups + '<span class="decimal-ellipsis">…</span></p>'
      + '<p class="decimal-example-caption"><strong>Last clean ×3 value: <span class="decimal-last">' + lastClean.raw + ' = 3<sup>' + (firstChangedIndex - 1) + '</sup></span>.</strong> The next power is <span class="decimal-expected">' + first.raw + '</span>; the decimal prints <strong class="decimal-actual">' + formatWord(first.word, base) + '</strong> and keeps going.</p>'
      + '</article>';
  }).join("\n");
}

export function renderPowerStack(): string {
  const groupHeadings = Array.from(
    { length: STACK_LAST_GROUP - STACK_FIRST_GROUP + 1 },
    (_, offset) => '<th scope="col">' + (STACK_FIRST_GROUP + offset) + '</th>',
  ).join("");
  const rows = POWER_STACK.map(row => {
    const cells = row.cells.map(cell => cell === null
      ? '<td class="stack-empty"></td>'
      : '<td>' + formatWord(cell, 1000n) + '</td>').join("");
    return '<tr data-exponent="' + row.exponent + '"><th scope="row"><span>3<sup>' + row.exponent + '</sup></span><small>= ' + row.power + '</small></th>' + cells + '</tr>';
  }).join("\n");
  const result = POWER_STACK_RESULT.map(word => '<td>' + formatWord(word, 1000n) + '</td>').join("")
    + '<td class="stack-continues" aria-label="The addition continues in later rows">…</td>';
  const additions = POWER_STACK_RESULT.slice(2).map((word, offset) => {
    const group = STACK_FIRST_GROUP + offset + 2;
    const pieces = POWER_STACK.flatMap(row => {
      const cell = row.cells[group - STACK_FIRST_GROUP];
      return cell === null || cell === undefined ? [] : [formatWord(cell, 1000n)];
    });
    return '<span><b>' + pieces.join(' + ') + '</b> = ' + formatWord(word, 1000n) + '</span>';
  }).join("");
  return '<p id="stack-scroll-note" class="stack-scroll-note" aria-hidden="true">Swipe to follow the groups <span>→</span></p>'
    + '<div class="power-stack-scroll" tabindex="0" aria-label="Horizontally scrollable addition table">'
    + '<table class="power-stack-table"><caption class="sr-only">Powers of three written at full width and aligned with decimal groups 5 through 12; completed sums are shown through group 11</caption>'
    + '<thead><tr><th scope="col">Whole power</th>' + groupHeadings + '</tr></thead><tbody>' + rows + '</tbody>'
    + '<tfoot><tr><th scope="row">Decimal</th>' + result + '</tr></tfoot></table></div>'
    + '<div class="stack-additions" aria-label="Column additions that produce the first five changed groups">' + additions + '</div>';
}
