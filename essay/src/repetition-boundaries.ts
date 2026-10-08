import { formatWord, recurrenceTrace } from "./math/lifts.ts";
import type { TraceRow } from "./math/lifts.ts";

export interface DivisionStep {
  readonly index: number;
  readonly remainder: bigint;
  readonly word: bigint;
  readonly nextRemainder: bigint;
}

export interface DivisionCycle {
  readonly preperiod: number;
  readonly period: number;
  /** One transient followed by one complete cycle, with no duplicate final state. */
  readonly rows: readonly DivisionStep[];
  readonly repeatRemainder: bigint;
}

export interface DecimalCycle extends DivisionCycle {
  readonly prefix: string;
  readonly cycle: string;
}

export interface GroupedEndpoint {
  /** Zero-based word position, also the raw power's exponent. */
  readonly wordIndex: number;
  readonly power: bigint;
  readonly word: bigint;
  readonly wordText: string;
  readonly remainderBefore: bigint;
  readonly remainderAfter: bigint;
  /** Includes any transient words and the initial coefficient k^0 = 1. */
  readonly coefficientCount: number;
}

export interface DecimalEndpoint extends GroupedEndpoint {
  /** Count of digits through the first full repetend, including the transient. */
  readonly position: number;
  /** Number of digits before the boundary within its word: 1 through width. */
  readonly split: number;
  readonly endingPart: string;
  readonly followingPart: string;
  readonly beforeDigits: string;
  readonly afterDigits: string;
}

export interface RepetitionBoundary {
  readonly denominator: bigint;
  readonly width: number;
  readonly base: bigint;
  readonly multiplier: bigint;
  readonly decimal: DecimalCycle;
  readonly grouped: DivisionCycle;
  readonly firstChangedIndex: number;
  readonly lastUnchangedIndex: number;
  readonly firstChangedRow: TraceRow;
  /** Remainders here surround the FINAL DECIMAL DIGIT, not its containing word. */
  readonly decimalEnd: DecimalEndpoint;
  readonly groupedEnd: GroupedEndpoint;
}

/**
 * Detect repetition by ordinary long division, independent of raw powers or
 * a presumed period. Bounded indices alone use number; all arithmetic is bigint.
 */
function divisionCycle(denominator: bigint, base: bigint): DivisionCycle {
  const seen = new Map<bigint, number>();
  const rows: DivisionStep[] = [];
  let remainder = 1n;
  while (!seen.has(remainder)) {
    if (remainder === 0n) throw new RangeError("This comparison requires a repeating reciprocal.");
    if (rows.length >= 100_000) throw new RangeError("The cycle exceeds the curated model's 100000-step limit.");
    seen.set(remainder, rows.length);
    const shifted = base * remainder;
    const nextRemainder = shifted % denominator;
    rows.push({ index: rows.length, remainder, word: shifted / denominator, nextRemainder });
    remainder = nextRemainder;
  }
  const preperiod = seen.get(remainder)!;
  return { preperiod, period: rows.length - preperiod, rows, repeatRemainder: remainder };
}

/**
 * Exact, computed examples for the three separate landmarks in the essay.
 * Periods are measured independently in base 10 and in base 10^width.
 * The power attached to an endpoint labels its position; it does not truncate
 * the infinite series. See the existing finite-prefix certificate for its tail.
 */
export function buildRepetitionBoundary(denominator: bigint, width: number): RepetitionBoundary {
  if (!Number.isSafeInteger(width) || width < 1 || width > 6) {
    throw new RangeError("The decimal word width must be an integer from 1 through 6.");
  }
  const base = 10n ** BigInt(width);
  const multiplier = base - denominator;
  if (denominator < 2n || multiplier < 2n) {
    throw new RangeError("Choose 2 <= denominator <= 10^width - 2.");
  }

  const decimalDivision = divisionCycle(denominator, 10n);
  const digits = decimalDivision.rows.map(row => String(row.word)).join("");
  const decimal: DecimalCycle = {
    ...decimalDivision,
    prefix: digits.slice(0, decimalDivision.preperiod),
    cycle: digits.slice(decimalDivision.preperiod),
  };
  const grouped = divisionCycle(denominator, base);
  const trace = recurrenceTrace({ base, coefficients: [multiplier] }, grouped.rows.length);
  for (const step of grouped.rows) {
    const row = trace.rows[step.index]!;
    if (row.word !== step.word || row.remainder !== step.remainder || row.nextRemainder !== step.nextRemainder) {
      throw new Error("The grouped cycle disagrees with the exact recurrence trace.");
    }
  }
  const firstChangedIndex = trace.firstChangedIndex;
  if (firstChangedIndex === null) throw new Error("The first corrected word was not reached within one cycle.");

  function endpoint(wordIndex: number): GroupedEndpoint {
    const row = trace.rows[wordIndex]!;
    return {
      wordIndex,
      power: row.raw,
      word: row.word,
      wordText: formatWord(row.word, base),
      remainderBefore: row.remainder,
      remainderAfter: row.nextRemainder,
      coefficientCount: wordIndex + 1,
    };
  }

  const position = decimal.rows.length;
  const wordIndex = Math.floor((position - 1) / width);
  const split = (position - 1) % width + 1;
  const containingWord = endpoint(wordIndex);
  const lastDigit = decimal.rows.at(-1)!;
  const decimalEnd: DecimalEndpoint = {
    ...containingWord,
    position,
    split,
    endingPart: containingWord.wordText.slice(0, split),
    followingPart: containingWord.wordText.slice(split),
    beforeDigits: decimal.cycle.slice(-9),
    afterDigits: decimal.cycle.repeat(Math.ceil(6 / decimal.period)).slice(0, 6),
    remainderBefore: lastDigit.remainder,
    remainderAfter: lastDigit.nextRemainder,
  };

  return {
    denominator, width, base, multiplier, decimal, grouped,
    firstChangedIndex,
    lastUnchangedIndex: firstChangedIndex - 1,
    firstChangedRow: trace.rows[firstChangedIndex]!,
    decimalEnd,
    groupedEnd: endpoint(grouped.rows.length - 1),
  };
}

/** Curated examples only; no arbitrary-input UI or period claims are inferred. */
export const REPETITION_BOUNDARIES = [
  buildRepetitionBoundary(97n, 2),
  buildRepetitionBoundary(997n, 3),
  buildRepetitionBoundary(94n, 2),
  buildRepetitionBoundary(994n, 3),
];
