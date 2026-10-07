import { OPENING_EXAMPLES } from "../src/opening-examples.ts";
import { formatWord } from "../src/math/lifts.ts";

/** Render exact curated examples at build time so they are visible without JS. */
export function renderOpeningExamples(): string {
  return OPENING_EXAMPLES.map(example => {
    const { denominator, base, width, rows, firstChangedIndex } = example;
    const first = rows[firstChangedIndex]!;
    const groups = rows.map((row, index) => {
      const kind = index < firstChangedIndex ? "pattern" : index === firstChangedIndex ? "change" : "later";
      const digits = formatWord(row.word, base);
      return '<span class="decimal-group decimal-' + kind + '" data-kind="' + kind + '" data-word="' + digits + '">' + digits + '</span>';
    }).join(" ");
    return '<article class="decimal-example" data-denominator="' + denominator + '" data-width="' + width + '">'
      + '<div class="decimal-example-heading"><h3>1/' + denominator + '</h3>'
      + '<span>' + denominator + ' = ' + base + ' − 3</span><span class="decimal-width">' + width + '-digit groups</span></div>'
      + '<p class="decimal-expansion" aria-label="First sixteen ' + width + '-digit groups of one over ' + denominator + '"><span class="decimal-point">0.</span> ' + groups + ' <span class="decimal-ellipsis">…</span></p>'
      + '<p class="decimal-example-caption"><strong>' + firstChangedIndex + ' groups follow ×3.</strong> Then we expect <span class="decimal-expected">' + first.raw + '</span>, but get <strong class="decimal-actual">' + formatWord(first.word, base) + '</strong>.</p>'
      + '</article>';
  }).join("\n");
}
