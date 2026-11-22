/** The bounded base-1000 worked example used by the field lesson. */
const RADIX = 1000;
const FIRST_SHOWN = 968;
const LAST_SHOWN = 1033;
const GROUPS = 6;

export interface FieldReading {
  denominator: number;
  /** Signed offset 1000 − n, distinct from the ordinary remainder above 1000. */
  ratio: number;
  inField: boolean;
  /** Ordinary long-division words, including leading zeros and terminating zeros. */
  groups: string[];
  /** The second word predicted before an adjustment from later terms. */
  expectedSecond: number;
  actualSecond: number;
  /** Coefficients of 1/n = Σ ratio^j / 1000^(j+1), not printed words. */
  signedTerms: number[];
}

export function fieldReading(n: number): FieldReading {
  if (!Number.isSafeInteger(n) || n < FIRST_SHOWN || n > LAST_SHOWN) {
    throw new RangeError("Choose a whole-number denominator from 968 to 1033.");
  }
  const ratio = RADIX - n;
  const groups: string[] = [];
  let remainder = 1;
  for (let index = 0; index < GROUPS; index++) {
    const scaled = RADIX * remainder;
    const word = Math.floor(scaled / n);
    remainder = scaled - word * n;
    groups.push(String(word).padStart(3, "0"));
  }
  return {
    denominator: n,
    ratio,
    inField: ratio * ratio < n,
    groups,
    expectedSecond: ratio >= 0 ? ratio : RADIX + ratio,
    actualSecond: Number(groups[1]!),
    signedTerms: Array.from({ length: GROUPS }, (_, index) => ratio ** index),
  };
}

// Only drawing positions use square roots. Membership and division above use
// bounded integers; every intermediate value is exactly representable.
const discriminantRoot = Math.sqrt(4001);
const lowerRoot = (discriminantRoot - 1) / 2;
export const THOUSAND_FIELD = Object.freeze({
  lowerRoot,
  upperRoot: lowerRoot + 1,
  lower: (2001 - discriminantRoot) / 2,
  upper: (2001 + discriminantRoot) / 2,
  first: 969,
  last: 1032,
  count: 64,
});

/**
 * Position within the displayed 968..1033 range. Continuous values are allowed
 * here so that the true field boundaries can be drawn between integer dots.
 */
export function coordinate(n: number, scale: "number" | "root"): number {
  if (!Number.isFinite(n) || n < FIRST_SHOWN || n > LAST_SHOWN) {
    throw new RangeError("A plotted position must be between 968 and 1033.");
  }
  if (scale === "number") return (n - FIRST_SHOWN) / (LAST_SHOWN - FIRST_SHOWN);
  if (scale === "root") {
    return (Math.sqrt(n) - Math.sqrt(FIRST_SHOWN)) / (Math.sqrt(LAST_SHOWN) - Math.sqrt(FIRST_SHOWN));
  }
  throw new RangeError("Choose the number scale or the square-root scale.");
}
