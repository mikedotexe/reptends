import { recurrenceTrace } from "./math/lifts.ts";

/**
 * Curated, build-time examples for the opening decimal gallery.
 * Their printed words come from the same exact trace as the interactive essay;
 * the build renders them into HTML so the comparison also works without JS.
 */
export const OPENING_EXAMPLES = [2, 3, 4].map(width => {
  const base = 10n ** BigInt(width);
  const trace = recurrenceTrace({ base, coefficients: [3n] }, 16);
  const firstChangedIndex = trace.firstChangedIndex;
  if (firstChangedIndex === null) {
    throw new Error("Every opening example must show the first changed group.");
  }
  return {
    base,
    denominator: trace.denominator,
    width,
    rows: trace.rows,
    firstChangedIndex,
  };
});
