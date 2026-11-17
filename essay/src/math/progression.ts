import { advanceRun, type DivisionState, type RunResult } from "../run-radices.ts";

export type ProgressionExample = "powers" | "counting";

export interface ProgressionInfo {
  denominator: bigint;
  prefixLength: number;
  prefixLabel: string;
  patternLabel: string;
  firstDesired: bigint;
  initialRemainder: bigint;
}

const examples: Record<ProgressionExample, ProgressionInfo> = {
  powers: {
    denominator: 997n, prefixLength: 6,
    prefixLabel: "001 · 003 · 009 · 027 · 081 · 243",
    patternLabel: "Keep tripling", firstDesired: 729n, initialRemainder: 729n,
  },
  counting: {
    denominator: 998001n, prefixLength: 998,
    prefixLabel: "000 · 001 · 002 · … · 995 · 996 · 997",
    patternLabel: "Keep counting", firstDesired: 998n, initialRemainder: 997003n,
  },
};

export function progressionInfo(example: ProgressionExample): ProgressionInfo {
  if (!Object.hasOwn(examples, example)) throw new RangeError("Unknown progression example.");
  return { ...examples[example] };
}

/** Smallest radix emitting this positive digit with a positive remaining tail.
 * This rule is independent of the base used to display its integers.
 */
export function continueWithDigit(D: bigint, state: DivisionState, digit: bigint): RunResult {
  if (D <= 1n || state.remainder <= 0n || state.remainder >= D || digit <= 0n) {
    throw new RangeError("Continuation needs D > r > 0 and a positive next digit.");
  }
  const radix = D * digit / state.remainder + 1n;
  return advanceRun(D, state, { radix, length: 1 });
}

export interface ProgressionRow {
  index: number;
  position: number;
  denominator: bigint;
  desired: bigint;
  radix: bigint;
  before: DivisionState;
  after: DivisionState;
  /** Alternative base-1000 step from THIS incoming state, not an unchanged path. */
  ordinaryDigit: bigint;
  ordinaryRemainder: bigint;
}

export function progressionRows(example: ProgressionExample, count = 8): readonly ProgressionRow[] {
  if (!Number.isSafeInteger(count) || count < 1 || count > 169) {
    throw new RangeError("Choose 1–169 continuation steps.");
  }
  const info = progressionInfo(example);
  const prefix = advanceRun(info.denominator,
    { place: 1n, quotient: 0n, remainder: 1n },
    { radix: 1000n, length: info.prefixLength });
  let state = prefix.after;
  let desired = info.firstDesired;
  const rows: ProgressionRow[] = [];
  for (let index = 0; index < count; index++) {
    const run = continueWithDigit(info.denominator, state, desired);
    rows.push({
      index, position: info.prefixLength + index + 1, denominator: info.denominator,
      desired, radix: run.radix, before: run.before, after: run.after,
      ordinaryDigit: 1000n * state.remainder / info.denominator,
      ordinaryRemainder: 1000n * state.remainder % info.denominator,
    });
    state = run.after;
    desired = example === "powers" ? desired * 3n : desired + 1n;
  }
  return rows;
}
