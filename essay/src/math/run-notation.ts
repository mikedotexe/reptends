import { advanceRun } from "../run-radices.ts";
import { progressionInfo, progressionRows, type ProgressionExample } from "./progression.ts";

/** A displayed run: one radix for every successive digit in the brackets. */
export interface NotationRun { readonly radix: bigint; readonly digits: readonly bigint[] }

export function validateRun(run: NotationRun): void {
  if (run.radix < 2n || run.digits.length === 0 || run.digits.some(d => d < 0n || d >= run.radix)) {
    throw new RangeError("A run needs a radix of at least 2 and one or more legal digits.");
  }
}

/** Evaluate written digits only. An unfinished fraction still needs its tail. */
export function evaluateRuns(runs: readonly NotationRun[]) {
  let place = 1n, quotient = 0n;
  for (const run of runs) {
    validateRun(run);
    for (const digit of run.digits) {
      place *= run.radix;
      quotient = quotient * run.radix + digit;
    }
  }
  return { place, quotient };
}

export function progressionRuns(example: ProgressionExample, count = 3): readonly NotationRun[] {
  const info = progressionInfo(example);
  const prefix = advanceRun(info.denominator, {place:1n, quotient:0n, remainder:1n},
    {radix:info.originalRadix, length:info.prefixLength});
  return [{radix:prefix.radix, digits:prefix.digits}, ...progressionRows(example,count).map(row =>
    ({radix:row.radix, digits:[row.desired]}))];
}

/** Ellipsis is only used for the explicitly labeled consecutive counting run. */
export function runDigits(run: NotationRun, abbreviateCounting = false): string {
  validateRun(run);
  if (abbreviateCounting && run.digits.length > 12) {
    if (!run.digits.every((d,i) => d === BigInt(i))) throw new RangeError("Only a complete counting prefix may be abbreviated.");
    return `⟨${run.digits.slice(0,3).join(", ")}, …, ${run.digits.slice(-3).join(", ")}⟩`;
  }
  return `⟨${run.digits.join(", ")}⟩`;
}
