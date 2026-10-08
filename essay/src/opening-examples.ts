import { recurrenceTrace } from "./math/lifts.ts";

export const OPENING_GROUP_COUNT = 16;

/**
 * Curated, build-time examples for the opening decimal gallery.
 * Their printed words come from the same exact trace as the interactive essay;
 * the build renders them into HTML so the comparison also works without JS.
 */
export const OPENING_EXAMPLES = [2, 3, 4].map(width => {
  const base = 10n ** BigInt(width);
  const trace = recurrenceTrace({ base, coefficients: [3n] }, OPENING_GROUP_COUNT);
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

export const STACK_FIRST_GROUP = 5;
export const STACK_LAST_GROUP = 12;
export const STACK_RESULT_LAST_GROUP = 11;

function wordsInBase(value: bigint, base: bigint): bigint[] {
  const words: bigint[] = [];
  for (let remaining = value; remaining > 0n; remaining /= base) words.unshift(remaining % base);
  return words.length === 0 ? [0n] : words;
}

/**
 * Align 3^e / 1000^(e+1) by its original place while retaining every
 * base-1000 word of the numerator. This is the literal addition stack shown
 * in the essay; null means that term has no contribution in the column.
 */
export const POWER_STACK = Array.from({ length: 8 }, (_, offset) => {
  const exponent = offset + 4;
  const power = 3n ** BigInt(exponent);
  const words = wordsInBase(power, 1000n);
  const firstOccupiedGroup = exponent + 2 - words.length;
  const cells = Array.from({ length: STACK_LAST_GROUP - STACK_FIRST_GROUP + 1 }, (_, cellOffset) => {
    const group = STACK_FIRST_GROUP + cellOffset;
    return words[group - firstOccupiedGroup] ?? null;
  });
  return { exponent, power, firstOccupiedGroup, cells };
});

const stackTrace = recurrenceTrace({ base: 1000n, coefficients: [3n] }, STACK_RESULT_LAST_GROUP);
export const POWER_STACK_RESULT = stackTrace.rows
  .slice(STACK_FIRST_GROUP - 1, STACK_RESULT_LAST_GROUP)
  .map(row => row.word);
