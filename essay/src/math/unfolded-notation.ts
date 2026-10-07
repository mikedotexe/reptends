import { euclideanDivide, recurrenceTrace } from "./lifts.ts";
import type { RecurrenceSpec, RecurrenceTrace, TraceRow } from "./lifts.ts";

/** Display widths describe written decimal labels, never a change of radix. */
export interface UnfoldedRow extends TraceRow {
  /** Row m contributes raw / B^(m+1), including any seeded zero. */
  readonly placeIndex: number;
  /** Digits of |raw|, excluding the sign, with decimal-word padding if applicable. */
  readonly displayWidth: number;
  /** Announce a new record width; null means no new width announcement. */
  readonly widthMarker: number | null;
  readonly displayedTerm: string;
}

export interface UnfoldedView {
  readonly trace: RecurrenceTrace;
  /** B = 10^n uses n digits; all other bases start with a one-digit label. */
  readonly minimumDisplayWidth: number;
  readonly rows: readonly UnfoldedRow[];
}

function minimumDecimalWidth(base: bigint): number {
  let rest = base;
  let digits = 0;
  while (rest % 10n === 0n) {
    rest /= 10n;
    digits += 1;
  }
  return rest === 1n ? digits : 1;
}

/**
 * Keep oversized or signed raw terms intact while annotating their display.
 * An increased label width does NOT consume additional radix positions.
 * For nondecimal-power B, the decimal label is not a decimal-expansion block.
 */
export function buildUnfoldedView(spec: RecurrenceSpec, steps = 16): UnfoldedView {
  const trace = recurrenceTrace(spec, steps);
  const minimumDisplayWidth = minimumDecimalWidth(trace.base);
  let greatestWidth = minimumDisplayWidth;
  const rows = trace.rows.map((row): UnfoldedRow => {
    const magnitude = (row.raw < 0n ? -row.raw : row.raw).toString();
    const displayWidth = Math.max(minimumDisplayWidth, magnitude.length);
    const widthMarker = displayWidth > greatestWidth ? displayWidth : null;
    greatestWidth = Math.max(greatestWidth, displayWidth);
    return {
      ...row,
      placeIndex: row.index + 1,
      displayWidth,
      widthMarker,
      displayedTerm: `${row.raw < 0n ? "−" : ""}${magnitude.padStart(displayWidth, "0")}`,
    };
  });
  return { trace, minimumDisplayWidth, rows };
}

export interface ExactFraction {
  readonly numerator: bigint;
  readonly denominator: bigint;
}

export interface FinitePrefixCertificate {
  readonly terms: number;
  /** Sum of the first M raw contributions, with common denominator B^M. */
  readonly prefix: ExactFraction;
  /** Exact remaining balance x_M / (D B^M), possibly signed or growing. */
  readonly residual: ExactFraction;
  readonly original: ExactFraction;
  readonly stateAfterPrefix: bigint;
  /** Whole denominator copies carried back across the finite prefix boundary. */
  readonly boundaryCarry: bigint;
  /** The normalized first M words interpreted as one base-B integer. */
  readonly settledPrefixInteger: bigint;
  readonly canonicalRemainder: bigint;
  /** D * prefix.numerator + x_M = U * B^M, verified before returning. */
  readonly identity: {
    readonly left: bigint;
    readonly right: bigint;
  };
}

/**
 * A finite identity, valid even when the infinite raw-term series diverges.
 * Fractions deliberately retain the common place-value denominator; they are
 * not reduced, because that denominator explains each term's position.
 */
export function certifiedPrefix(trace: RecurrenceTrace, terms: number): FinitePrefixCertificate {
  if (!Number.isSafeInteger(terms) || terms < 0 || terms > trace.rows.length) {
    throw new RangeError("terms must be an integer from 0 through the trace length.");
  }
  let prefixNumerator = 0n;
  for (let index = 0; index < terms; index += 1) {
    prefixNumerator = trace.base * prefixNumerator + trace.rows[index]!.raw;
  }
  const basePower = trace.base ** BigInt(terms);
  const stateAfterPrefix = terms === 0 ? trace.numerator : trace.rows[terms - 1]!.nextLift;
  const left = trace.denominator * prefixNumerator + stateAfterPrefix;
  const right = trace.numerator * basePower;
  if (left !== right) {
    throw new Error("The finite raw prefix and residual do not equal the original fraction.");
  }
  const boundary = euclideanDivide(stateAfterPrefix, trace.denominator);
  const settledPrefixInteger = prefixNumerator + boundary.quotient;
  const ordinary = euclideanDivide(right, trace.denominator);
  if (settledPrefixInteger !== ordinary.quotient || boundary.remainder !== ordinary.remainder) {
    throw new Error("The carried prefix disagrees with ordinary division.");
  }
  return {
    terms,
    prefix: { numerator: prefixNumerator, denominator: basePower },
    residual: { numerator: stateAfterPrefix, denominator: trace.denominator * basePower },
    original: { numerator: trace.numerator, denominator: trace.denominator },
    stateAfterPrefix,
    boundaryCarry: boundary.quotient,
    settledPrefixInteger,
    canonicalRemainder: boundary.remainder,
    identity: { left, right },
  };
}
