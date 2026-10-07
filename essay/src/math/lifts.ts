/**
 * One arithmetic transition, expressed in three coordinate systems.
 * BigInt is essential: growing lifts must not be rounded to floating point.
 * This module has no platform dependencies and can also power a browser UI.
 */

export interface EuclideanDivision {
  readonly quotient: bigint;
  readonly remainder: bigint;
}

/** Unlike JavaScript's / and %, this gives a nonnegative remainder for n < 0. */
export function euclideanDivide(n: bigint, denominator: bigint): EuclideanDivision {
  if (denominator <= 0n) throw new RangeError("The denominator must be positive.");
  let quotient = n / denominator;
  let remainder = n % denominator;
  if (remainder < 0n) {
    quotient -= 1n;
    remainder += denominator;
  }
  return { quotient, remainder };
}

export interface Transition {
  readonly lift: bigint;
  readonly nextLift: bigint;
  readonly quotient: bigint;
  readonly nextQuotient: bigint;
  readonly remainder: bigint;
  readonly nextRemainder: bigint;
  readonly raw: bigint;
  readonly carryIn: bigint;
  readonly currentStripAdjustment: bigint;
  readonly word: bigint;
}

function validateDivision(base: bigint, denominator: bigint): void {
  if (base < 2n) throw new RangeError("The word base must be at least 2.");
  if (denominator < 2n) throw new RangeError("The denominator must be at least 2.");
}

/**
 * Coherence means nextLift ≡ base * lift (mod denominator).
 * The raw emission and quotient coordinates may be arbitrarily large or signed;
 * their normalized output is always a legal word, 0 <= word < base.
 */
export function normalizeTransition(
  base: bigint,
  denominator: bigint,
  lift: bigint,
  nextLift: bigint,
): Transition {
  validateDivision(base, denominator);
  const difference = base * lift - nextLift;
  if (difference % denominator !== 0n) {
    throw new RangeError("These lifted states do not follow the same remainder orbit.");
  }

  const current = euclideanDivide(lift, denominator);
  const next = euclideanDivide(nextLift, denominator);
  const raw = difference / denominator;
  const carryIn = next.quotient;
  const currentStripAdjustment = -base * current.quotient;

  // The central identity: raw + next strip number - base * current strip number.
  const word = raw + carryIn + currentStripAdjustment;

  // An independently computed ordinary long-division step must agree exactly.
  const ordinary = euclideanDivide(base * current.remainder, denominator);
  if (word !== ordinary.quotient || next.remainder !== ordinary.remainder) {
    throw new Error("The lift and long-division descriptions disagree.");
  }
  if (word < 0n || word >= base) throw new Error("The normalized word is out of range.");

  return {
    lift, nextLift,
    quotient: current.quotient,
    nextQuotient: next.quotient,
    remainder: current.remainder,
    nextRemainder: next.remainder,
    raw, carryIn, currentStripAdjustment, word,
  };
}

export interface RecurrenceSpec {
  readonly base: bigint;
  /** P(X) = X^d - c[0] X^(d-1) - ... - c[d-1]. */
  readonly coefficients: readonly bigint[];
  readonly numerator?: bigint;
}

export interface TraceRow extends Transition {
  /** Zero-based: row 0 emits the very first word, including any seeded zero. */
  readonly index: number;
  /** Coefficients of X^index modulo P, lowest power first, scaled by numerator. */
  readonly polynomial: readonly bigint[];
}

export interface RecurrenceTrace {
  readonly base: bigint;
  readonly denominator: bigint;
  readonly numerator: bigint;
  readonly coefficients: readonly bigint[];
  readonly rows: readonly TraceRow[];
  /** null means not encountered within this finite trace, not "never happens". */
  readonly firstChangedIndex: number | null;
  /** Output-row index m whose NEXT state x_(m+1) first exits [0, denominator). */
  readonly firstExitIndex: number | null;
}

function evaluate(polynomial: readonly bigint[], base: bigint): bigint {
  return polynomial.reduceRight((sum, coefficient) => sum * base + coefficient, 0n);
}

export function recurrenceDenominator(spec: RecurrenceSpec): bigint {
  if (spec.base < 2n) throw new RangeError("The word base must be at least 2.");
  if (spec.coefficients.length === 0 || spec.coefficients.length > 64) {
    throw new RangeError("Provide between 1 and 64 recurrence coefficients.");
  }
  // Horner evaluation of the monic characteristic polynomial at the word base.
  const denominator = spec.coefficients.reduce((value, c) => value * spec.base - c, 1n);
  validateDivision(spec.base, denominator);
  return denominator;
}

export function recurrenceTrace(spec: RecurrenceSpec, steps = 25): RecurrenceTrace {
  if (!Number.isSafeInteger(steps) || steps < 0 || steps > 100_000) {
    throw new RangeError("steps must be an integer from 0 through 100000.");
  }
  const base = spec.base;
  const coefficients = [...spec.coefficients];
  const denominator = recurrenceDenominator(spec);
  const numerator = spec.numerator ?? 1n;
  if (numerator <= 0n || numerator >= denominator) {
    throw new RangeError("The numerator must satisfy 0 < numerator < denominator.");
  }

  const degree = coefficients.length;
  let polynomial = Array<bigint>(degree).fill(0n);
  polynomial[0] = numerator;
  let ordinaryRemainder = numerator;
  const rows: TraceRow[] = [];
  const rawTerms: bigint[] = [];
  let firstChangedIndex: number | null = null;
  let firstExitIndex: number | null = null;

  for (let index = 0; index < steps; index += 1) {
    const raw = polynomial[degree - 1]!;
    const nextPolynomial = Array<bigint>(degree).fill(0n);

    // Multiply by X, then replace X^d by c[0]X^(d-1) + ... + c[d-1].
    for (let j = 1; j < degree; j += 1) nextPolynomial[j] = polynomial[j - 1]!;
    coefficients.forEach((coefficient, j) => {
      const position = degree - j - 1;
      nextPolynomial[position] = nextPolynomial[position]! + raw * coefficient;
    });

    const row: TraceRow = {
      ...normalizeTransition(base, denominator, evaluate(polynomial, base), evaluate(nextPolynomial, base)),
      index,
      polynomial: [...polynomial],
    };

    // Check against the seeded recurrence, not just polynomial reduction.
    const independentRaw = index < degree - 1 ? 0n : index === degree - 1 ? numerator
      : coefficients.reduce((sum, c, j) => sum + c * rawTerms[index - j - 1]!, 0n);
    if (row.raw !== raw || raw !== independentRaw) throw new Error("The raw recurrence check failed.");

    // This path never uses the lifted integer or a carry coordinate.
    const ordinary = euclideanDivide(base * ordinaryRemainder, denominator);
    if (row.remainder !== ordinaryRemainder || row.word !== ordinary.quotient || row.nextRemainder !== ordinary.remainder) {
      throw new Error("The independent long-division trace disagrees.");
    }

    if (firstChangedIndex === null && row.word !== raw) firstChangedIndex = index;
    if (firstExitIndex === null && (row.nextLift < 0n || row.nextLift >= denominator)) firstExitIndex = index;
    rows.push(row);
    rawTerms.push(raw);
    polynomial = nextPolynomial;
    ordinaryRemainder = ordinary.remainder;
  }
  if (firstChangedIndex !== firstExitIndex) throw new Error("The first-exit theorem check failed.");
  return { base, denominator, numerator, coefficients, rows, firstChangedIndex, firstExitIndex };
}

/** Choose the remainder itself as the lift: all quotient coordinates become zero. */
export function canonicalView(base: bigint, denominator: bigint, row: Transition): Transition {
  return normalizeTransition(base, denominator, row.remainder, row.nextRemainder);
}

/** Render decimal-power words with their leading zeros; other bases use [value]. */
export function formatWord(word: bigint, base: bigint): string {
  if (base < 2n || word < 0n || word >= base) throw new RangeError("Illegal word or base.");
  let value = base;
  let digits = 0;
  while (value % 10n === 0n) { value /= 10n; digits += 1; }
  return value === 1n ? word.toString().padStart(digits, "0") : `[${word}]`;
}
