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
