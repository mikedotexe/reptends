import type { TraceRow } from "./math/lifts.ts";

interface DecimalStep {
  readonly position: number;
  readonly digit: bigint;
  readonly remainder: bigint;
  readonly nextRemainder: bigint;
}

export interface DecimalReturn {
  readonly position: number;
  readonly copy: number;
  readonly afterDigits: number;
  readonly before: string;
  readonly after: string;
  readonly steps: readonly DecimalStep[];
}

/**
 * The curated 1/997 explorer uses three-digit words and has a 166-digit period.
 * Find returns by ordinary one-digit division, not by a display-position lookup.
 * The period and all six returns in the two grouped cycles have independent tests.
 */
export function decimalReturn997(row: Pick<TraceRow, "index" | "remainder" | "word" | "nextRemainder">): DecimalReturn | null {
  if (!Number.isInteger(row.index) || row.index < 0 || row.index >= 332) {
    throw new RangeError("The curated explorer contains groups 1 through 332.");
  }
  const steps: DecimalStep[] = [];
  let remainder = row.remainder;
  let digits = "";
  let afterDigits = 0;
  for (let offset = 1; offset <= 3; offset++) {
    const scaled = 10n * remainder;
    const digit = scaled / 997n;
    const nextRemainder = scaled % 997n;
    if (digit < 0n || digit > 9n || nextRemainder < 0n) {
      throw new Error("A decimal step must emit one digit and a nonnegative remainder.");
    }
    steps.push({ position: row.index * 3 + offset, digit, remainder, nextRemainder });
    digits += String(digit);
    remainder = nextRemainder;
    if (remainder === 1n) afterDigits = offset;
  }
  if (BigInt(digits) !== row.word || remainder !== row.nextRemainder) {
    throw new Error("Digitwise division must agree with the selected three-digit step.");
  }
  if (!afterDigits) return null;
  const position = row.index * 3 + afterDigits;
  if (position % 166 !== 0) throw new Error("The remainder returned outside the verified 166-digit period.");
  return {
    position,
    copy: position / 166,
    afterDigits,
    before: digits.slice(0, afterDigits),
    after: digits.slice(afterDigits),
    steps,
  };
}
