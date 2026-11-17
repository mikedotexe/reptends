import { advanceRun, type DivisionState, type RunResult } from "../run-radices.ts";

export type ProgressionExample = "powers" | "fibonacci" | "counting";
export const progressionExamples: readonly ProgressionExample[] = ["powers", "fibonacci", "counting"];
const specs = {
  powers: { denominator: 997n, originalRadix: 1000n, patternLabel: "Keep tripling", origin: "1000 − 997 = 3. The coefficients triple: 1, 3, 9, 27… ." },
  fibonacci: { denominator: 9899n, originalRadix: 100n, patternLabel: "Keep adding the previous two", origin: "9899 = 100² − 100 − 1. The coefficients are Fibonacci numbers: 0, 1, 1, 2, 3, 5… ." },
  counting: { denominator: 998001n, originalRadix: 1000n, patternLabel: "Keep counting", origin: "998001 = 999². The coefficients count upward: 0, 1, 2, 3… ." },
};

/** The one state transition used from the first digit onward. A zero balance
 * completes the expansion; negative balances retain their sign. Rejected zero
 * targets are outside the positive-target fallback's domain. */
export function balanceStep(D: bigint, state: DivisionState, currentRadix: bigint, desired: bigint) {
  if (D <= 1n || currentRadix < 2n || state.remainder <= 0n || state.remainder >= D || desired < 0n) {
    throw new RangeError("A balance check needs a valid radix, a proper positive remainder, and a nonnegative term.");
  }
  const candidate = currentRadix * state.remainder - D * desired;
  const fits = candidate >= 0n && candidate < D;
  if (!fits && desired === 0n) throw new RangeError("A rejected zero term needs a separate radix choice.");
  const radix = fits ? currentRadix : D * desired / state.remainder + 1n;
  const run = advanceRun(D, state, { radix, length: 1 });
  return { ...run, currentRadix, candidate, action: run.after.remainder === 0n ? "finish" as const : fits ? "keep" as const : "change" as const };
}

/** Earlier strictly positive-tail construction, retained for existing users. */
export function continueWithDigit(D: bigint, state: DivisionState, digit: bigint): RunResult {
  if (D <= 1n || state.remainder <= 0n || state.remainder >= D || digit <= 0n) {
    throw new RangeError("Continuation needs D > r > 0 and a positive next digit.");
  }
  return advanceRun(D, state, { radix: D * digit / state.remainder + 1n, length: 1 });
}

export interface ProgressionRow {
  index: number; position: number; denominator: bigint; desired: bigint;
  radix: bigint; currentRadix: bigint; candidate: bigint; action: "keep" | "change" | "finish";
  before: DivisionState; after: DivisionState;
  ordinaryDigit: bigint; ordinaryRemainder: bigint;
}

function* coefficients(example: ProgressionExample): Generator<bigint> {
  let a = example === "powers" ? 1n : 0n;
  let b = 1n;
  while (true) {
    yield a;
    if (example === "powers") a *= 3n;
    else if (example === "counting") a++;
    else [a, b] = [b, a + b];
  }
}

/** Find the first change with the balance check itself, without a stored boundary
 * or a parallel ordinary-division stream. Preserve the last accepted step. */
function trace(example: ProgressionExample, count: number) {
  if (!Object.hasOwn(specs, example)) throw new RangeError("Unknown progression example.");
  const spec = specs[example];
  let state: DivisionState = { place: 1n, quotient: 0n, remainder: 1n };
  let radix = spec.originalRadix;
  let previous: ProgressionRow | undefined;
  const prefix: bigint[] = [];
  const rows: ProgressionRow[] = [];
  let firstChanged = false;
  let position = 0;
  let lastKept: ProgressionRow | undefined;
  for (const desired of coefficients(example)) {
    if (++position > 4096) throw new RangeError("Example did not reach the requested window within 4096 positions.");
    const step = balanceStep(spec.denominator, state, radix, desired);
    const row: ProgressionRow = {
      index: firstChanged ? rows.length : 0, position, denominator: spec.denominator, desired,
      radix: step.radix, currentRadix: radix, candidate: step.candidate, action: step.action,
      before: step.before, after: step.after,
      ordinaryDigit: spec.originalRadix * state.remainder / spec.denominator,
      ordinaryRemainder: spec.originalRadix * state.remainder % spec.denominator,
    };
    if (!firstChanged && step.action === "change") { firstChanged = true; lastKept = previous; }
    if (firstChanged) rows.push(row); else prefix.push(desired);
    if (rows.length === count) {
      if (!lastKept) throw new Error("These examples require an accepted prefix.");
      return { rows, lastKept: { ...lastKept, index: -1 }, prefix };
    }
    if (step.action === "finish") throw new Error("This example completed before the requested continuation.");
    state = step.after; radix = step.radix; previous = row;
  }
  throw new Error("Unreachable coefficient stream end.");
}

export function progressionRows(example: ProgressionExample, count = 8): readonly ProgressionRow[] {
  if (!Number.isSafeInteger(count) || count < 1 || count > 169) throw new RangeError("Choose 1–169 continuation steps.");
  return trace(example, count).rows;
}
export function progressionBefore(example: ProgressionExample): ProgressionRow { return trace(example, 1).lastKept; }
export function progressionInfo(example: ProgressionExample) {
  const { rows, prefix } = trace(example, 1);
  const spec = specs[example];
  const width = spec.originalRadix === 100n ? 2 : 3;
  const format = (v: bigint) => v.toString().padStart(width, "0");
  const labels = prefix.length > 12 ? [...prefix.slice(0, 3).map(format), "…", ...prefix.slice(-3).map(format)] : prefix.map(format);
  return { ...spec, prefixLength: prefix.length, prefixLabel: labels.join(" · "), firstDesired: rows[0]!.desired, initialRemainder: rows[0]!.before.remainder };
}
