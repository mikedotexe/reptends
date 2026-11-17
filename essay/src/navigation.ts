/** Public links use one-based group numbers; the arithmetic trace is zero-based. */
export function positionFromSearch(search: string): number | null {
  const values = new URLSearchParams(search).getAll("group");
  if (values.length !== 1 || !/^[1-9][0-9]{0,2}$/.test(values[0]!)) return null;
  const group = Number(values[0]);
  return group <= 332 ? group - 1 : null;
}

export function linkToPosition(index: number): string {
  if (!Number.isSafeInteger(index) || index < 0 || index > 331) {
    throw new RangeError("The shared position must be within the two displayed cycles.");
  }
  return "https://reptends.mikedotexe.com/?group=" + (index + 1) + "#repeat";
}

/** Run numbers are one-based publicly; their power exponents are zero-based. */
export function runFromSearch(search: string): number | null {
  const values = new URLSearchParams(search).getAll("run");
  if (values.length !== 1 || !/^[1-9][0-9]{0,2}$/.test(values[0]!)) return null;
  const run = Number(values[0]);
  return run <= 169 ? run - 1 : null;
}

export function linkToRun(index: number): string {
  if (!Number.isSafeInteger(index) || index < 0 || index > 168) {
    throw new RangeError("The shared run must be within the 169 displayed positions.");
  }
  return "https://reptends.mikedotexe.com/?run=" + (index + 1) + "#change-radix";
}
