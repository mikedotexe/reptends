/** Exact mixed-radix accounting. Display bases never enter these operations. */
export interface DivisionState {
  place: bigint;
  quotient: bigint;
  remainder: bigint;
}
export interface RunSpec { radix: bigint; length: number }
export interface RunResult {
  before: DivisionState;
  after: DivisionState;
  radix: bigint;
  length: number;
  digits: readonly bigint[];
  packed: bigint;
  scale: bigint;
  firstReturn: boolean;
}

export function advanceRun(D: bigint, state: DivisionState, run: RunSpec): RunResult {
  if (D <= 1n || state.place <= 0n || state.quotient < 0n ||
      state.remainder < 0n || state.remainder >= D || run.radix < 2n ||
      !Number.isSafeInteger(run.length) || run.length < 1 || run.length > 1000) {
    throw new RangeError("A run needs a valid state, radix at least two, and 1–1000 positions.");
  }
  let remainder = state.remainder;
  let packed = 0n;
  let scale = 1n;
  let earlierReturn = false;
  const digits: bigint[] = [];
  for (let j = 0; j < run.length; j++) {
    const scaled = run.radix * remainder;
    const digit = scaled / D;
    remainder = scaled % D;
    digits.push(digit);
    packed = packed * run.radix + digit;
    scale *= run.radix;
    if (j + 1 < run.length && remainder === state.remainder) earlierReturn = true;
  }
  return {
    before: { ...state }, after: {
      place: state.place * scale,
      quotient: state.quotient * scale + packed,
      remainder,
    },
    ...run, digits, packed, scale,
    firstReturn: remainder === state.remainder && !earlierReturn,
  };
}

export function powerRuns(D: bigint, c: bigint, count: number): readonly RunResult[] {
  if (D <= 1n || c < 2n || !Number.isSafeInteger(count) || count < 0 || count > 169) {
    throw new RangeError("The power example needs D > 1, c ≥ 2, and 0–169 runs.");
  }
  let state: DivisionState = { place: 1n, quotient: 0n, remainder: 1n };
  let power = 1n;
  const result: RunResult[] = [];
  for (let n = 0; n < count; n++) {
    const row = advanceRun(D, state, { radix: D * power + 1n, length: 1 });
    result.push(row);
    state = row.after;
    power *= c;
  }
  return result;
}

/** Truncation, never rounding. The unfinished tail is recorded separately. */
export function decimalTruncation(numerator: bigint, denominator: bigint, places = 20): string {
  if (numerator < 0n || denominator <= 0n || !Number.isSafeInteger(places) || places < 1 || places > 30) {
    throw new RangeError("A decimal view needs a nonnegative fraction and 1–30 places.");
  }
  const scale = 10n ** BigInt(places);
  const value = numerator * scale / denominator;
  return `${value / scale}.${(value % scale).toString().padStart(places, "0")}`;
}
