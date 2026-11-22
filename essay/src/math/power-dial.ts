/** Bounded examples for changing a denominator and regrouping a fixed fraction. */
export interface PowerReading {
  width: number;
  base: number;
  denominator: number;
  quotient: number;
  remainder: number;
  /** Number of initial groups equal to q, qk, qk², … before any carry changes one. */
  cleanCount: number;
  /** One-based position of the first changed group. */
  firstChangedPosition: number;
  expected: number;
  actual: number;
  carry: number;
  /** k^(cleanCount + 1): the tail numerator that causes the first change. */
  nextPower: number;
  /** The clear opening plus its first changed group, including leading zeros. */
  groups: string[];
  coefficients: number[];
}

export interface PowerField {
  lower: number;
  upper: number;
  lowerRoot: number;
  upperRoot: number;
  first: number;
  last: number;
  count: number;
  ordinaryWidth: number;
}

export interface PowerFamilyReading extends PowerReading {
  field: PowerField;
}

export interface RegroupedReading extends PowerReading {
  /** The same first 60 decimal digits, partitioned into width-digit groups. */
  tapeGroups: string[];
}

function checkedWidth(width: number, first: number, last: number): void {
  if (!Number.isSafeInteger(width) || width < first || width > last) {
    throw new RangeError(`Choose a whole-number group width from ${first} to ${last}.`);
  }
}

function divide(base: number, denominator: number, width: number, count: number): string[] {
  const groups: string[] = [];
  let state = 1;
  for (let index = 0; index < count; index++) {
    const scaled = base * state;
    const digit = Math.floor(scaled / denominator);
    state = scaled - digit * denominator;
    groups.push(String(digit).padStart(width, "0"));
  }
  return groups;
}

/**
 * These examples have B = qn + k, q > 0 and 1 < k < n. Through the first
 * changed group, its printed value is qk^j + floor(k^(j+1)/n). The latter
 * term is the carry from the entire unprinted tail, not just the next term.
 * After this point coefficients may overflow; no later-word formula is claimed.
 * All integer intermediates in the exposed ranges are below 10^12.
 */
function reading(width: number, denominator: number): PowerReading {
  const base = 10 ** width;
  const quotient = Math.floor(base / denominator);
  const remainder = base - quotient * denominator;
  let cleanCount = 0;
  let nextPower = remainder;
  while (nextPower < denominator) {
    cleanCount++;
    nextPower *= remainder;
  }
  const coefficients = Array.from({ length: cleanCount + 1 }, (_, j) => quotient * remainder ** j);
  const groups = divide(base, denominator, width, cleanCount + 1);
  const expected = coefficients[cleanCount]!;
  const actual = Number(groups[cleanCount]!);
  return {
    width, base, denominator, quotient, remainder, cleanCount,
    firstChangedPosition: cleanCount + 1,
    expected, actual, carry: actual - expected, nextPower, groups, coefficients,
  };
}

function fieldAround(power: number): PowerField {
  // This is only a search window; integer membership determines both endpoints.
  const reach = Math.floor(Math.sqrt(power)) + 2;
  let first = power;
  let last = power;
  for (let n = power - reach; n <= power + reach; n++) {
    if ((power - n) ** 2 < n) {
      first = Math.min(first, n);
      last = Math.max(last, n);
    }
  }
  const discriminant = Math.sqrt(4 * power + 1);
  const lowerRoot = (discriminant - 1) / 2;
  return {
    lower: (2 * power + 1 - discriminant) / 2,
    upper: (2 * power + 1 + discriminant) / 2,
    lowerRoot,
    upperRoot: lowerRoot + 1,
    first, last, count: last - first + 1,
    ordinaryWidth: discriminant,
  };
}

/** Change both the power and denominator, keeping the gap equal to three. */
export function powerFamily(width: number): PowerFamilyReading {
  checkedWidth(width, 2, 6);
  const base = 10 ** width;
  return { ...reading(width, base - 3), field: fieldAround(base) };
}

/** Keep 1/997 fixed; change only the partition into decimal groups. */
export function regroup997(width: number): RegroupedReading {
  checkedWidth(width, 3, 6);
  const result = reading(width, 997);
  return { ...result, tapeGroups: divide(result.base, 997, width, 60 / width) };
}
