/** Exact indexed long division. All values and positions are integers. */
export const MAX_RANGE = 1000;
export const MAX_CHECK_POSITION = 100000n;

function requireBigInt(value: bigint, name: string): void {
  if (typeof value !== "bigint") throw new TypeError(`${name} must be an integer.`);
}

/**
 * Parse an unsigned integer without allowing an unbounded allocation first.
 * Separators are cosmetic. Powers and scientific notation have nonnegative
 * integer exponents; all intermediate products must fit the requested limit.
 */
export function parseWhole(text: string, name: string, maxDigits = 128): bigint {
  if (typeof text !== "string") throw new TypeError(`${name} must be text.`);
  if (!Number.isSafeInteger(maxDigits) || maxDigits < 1 || maxDigits > 1024) {
    throw new RangeError("The input limit must be between 1 and 1024 digits.");
  }
  if (text.length > maxDigits * 4 + 64) {
    throw new RangeError(`${name} is too long. Use at most ${maxDigits} digits.`);
  }
  const value = text.replace(/[\s,_]/g, "");
  const tooLarge = () => new RangeError(`${name} must fit within ${maxDigits} digits.`);
  const literal = (digits: string): bigint => {
    const canonical = digits.replace(/^0+/, "") || "0";
    if (canonical.length > maxDigits) throw tooLarge();
    return BigInt(canonical);
  };
  if (/^\d+$/.test(value)) return literal(value);
  const power = /^(\d+)(?:\^|\*\*)(\d+)$/.exec(value);
  const scientific = /^(\d+)e(\d+)$/i.exec(value);
  const match = power ?? scientific;
  if (!match) throw new RangeError(`${name} needs a whole number, such as 997 or 10^100.`);
  const exponentText = match[2]!.replace(/^0+/, "") || "0";
  if (exponentText.length > 4 || Number(exponentText) > 4096) {
    throw new RangeError(`${name} uses an exponent above this page's limit of 4096.`);
  }
  let exponent = BigInt(exponentText);
  const coefficient = literal(match[1]!);
  const limit = 10n ** BigInt(maxDigits) - 1n;
  const multiply = (left: bigint, right: bigint): bigint => {
    if (right !== 0n && left > limit / right) throw tooLarge();
    return left * right;
  };
  let factor = power ? coefficient : 10n;
  let result = power ? 1n : coefficient;
  // Zero remains zero; the exponent was still bounded before this shortcut.
  if (result === 0n) return 0n;
  while (exponent > 0n) {
    if (exponent & 1n) result = multiply(result, factor);
    exponent >>= 1n;
    if (exponent > 0n) factor = multiply(factor, factor);
  }
  if (result > limit) throw tooLarge();
  return result;
}

/** Repeated squaring computes a modular power without building B^exponent. */
export function modPow(base: bigint, exponent: bigint, modulus: bigint): bigint {
  requireBigInt(base, "Base");
  requireBigInt(exponent, "Exponent");
  requireBigInt(modulus, "Modulus");
  if (base < 0n || exponent < 0n || modulus < 1n) {
    throw new RangeError("A modular power needs a nonnegative base and exponent, and a positive modulus.");
  }
  let result = 1n % modulus;
  let factor = base % modulus;
  let remaining = exponent;
  while (remaining > 0n) {
    if (remaining & 1n) result = result * factor % modulus;
    remaining >>= 1n;
    if (remaining > 0n) factor = factor * factor % modulus;
  }
  return result;
}

function validatePosition(numerator: bigint, denominator: bigint, radix: bigint, position: bigint): void {
  for (const [name, value] of [["Numerator", numerator], ["Denominator", denominator], ["Radix", radix], ["Position", position]] as const) {
    requireBigInt(value, name);
  }
  if (numerator < 0n || denominator < 1n || radix < 2n || position < 1n) {
    throw new RangeError("Use a nonnegative numerator, denominator at least 1, radix at least 2, and position at least 1.");
  }
}

/** One-based position after the radix point; the integer part is separate. */
export function remainderBefore(numerator: bigint, denominator: bigint, radix: bigint, position: bigint): bigint {
  validatePosition(numerator, denominator, radix, position);
  return (numerator % denominator) * modPow(radix, position - 1n, denominator) % denominator;
}

export function digitAt(numerator: bigint, denominator: bigint, radix: bigint, position: bigint): bigint {
  return radix * remainderBefore(numerator, denominator, radix, position) / denominator;
}

export interface DigitWindowSpec {
  readonly numerator: bigint;
  readonly denominator: bigint;
  readonly radix: bigint;
  readonly start: bigint;
  readonly count: number;
}

export interface DigitWindow extends DigitWindowSpec {
  readonly remainderBefore: bigint;
  readonly digits: readonly bigint[];
  readonly remainderAfter: bigint;
  readonly integerPart: bigint;
}

/** Jump to the first requested position, then divide locally for the window. */
export function digitWindow(spec: DigitWindowSpec): DigitWindow {
  const { numerator, denominator, radix, start, count } = spec;
  validatePosition(numerator, denominator, radix, start);
  if (!Number.isSafeInteger(count) || count < 1 || count > MAX_RANGE) {
    throw new RangeError(`Request between 1 and ${MAX_RANGE} digits at a time.`);
  }
  const incoming = remainderBefore(numerator, denominator, radix, start);
  let remainder = incoming;
  const digits: bigint[] = [];
  for (let i = 0; i < count; i++) {
    const scaled = radix * remainder;
    digits.push(scaled / denominator);
    remainder = scaled % denominator;
  }
  return Object.freeze({
    numerator, denominator, radix, start, count,
    remainderBefore: incoming,
    digits: Object.freeze(digits),
    remainderAfter: remainder,
    integerPart: numerator / denominator,
  });
}

export interface LongDivisionOptions {
  readonly signal?: AbortSignal;
  readonly onProgress?: (completed: bigint) => void;
  readonly yieldControl?: () => Promise<void>;
}

export interface LongDivisionCheck {
  readonly status: "matched" | "mismatch" | "cancelled";
  readonly steps: bigint;
  readonly mismatchPosition?: bigint;
}

/**
 * Independent check: start at the initial remainder and walk every position.
 * This path never calls modular exponentiation or the indexed-digit helpers.
 */
export async function checkByLongDivision(
  expected: DigitWindow,
  options: LongDivisionOptions = {},
): Promise<LongDivisionCheck> {
  const { numerator, denominator, radix, start, count } = expected;
  validatePosition(numerator, denominator, radix, start);
  if (!Number.isSafeInteger(count) || count < 1 || count > MAX_RANGE || expected.digits.length !== count) {
    throw new RangeError("The expected window has an invalid digit count.");
  }
  const end = start + BigInt(count) - 1n;
  if (end > MAX_CHECK_POSITION) {
    throw new RangeError(`The sequential check stops at position ${MAX_CHECK_POSITION}. The indexed lookup has no such walk limit.`);
  }
  const digits = [...expected.digits];
  const incoming = expected.remainderBefore;
  const outgoing = expected.remainderAfter;
  const yieldControl = options.yieldControl ?? (() => new Promise<void>(resolve => setTimeout(resolve, 0)));
  let completed = 0n;
  let remainder = numerator % denominator;
  const cancelled = (): LongDivisionCheck => ({ status: "cancelled", steps: completed });
  while (completed < end) {
    if (options.signal?.aborted) return cancelled();
    const stop = completed + 1000n < end ? completed + 1000n : end;
    while (completed < stop) {
      const position = completed + 1n;
      if (position === start && remainder !== incoming) {
        return { status: "mismatch", steps: completed, mismatchPosition: start };
      }
      const scaled = radix * remainder;
      const digit = scaled / denominator;
      remainder = scaled % denominator;
      completed = position;
      if (position >= start && digit !== digits[Number(position - start)]) {
        return { status: "mismatch", steps: completed, mismatchPosition: position };
      }
    }
    options.onProgress?.(completed);
    if (options.signal?.aborted) return cancelled();
    if (completed < end) {
      await yieldControl();
      if (options.signal?.aborted) return cancelled();
    }
  }
  return remainder === outgoing ? { status: "matched", steps: completed }
    : { status: "mismatch", steps: completed, mismatchPosition: end };
}

/** Large-base digits are explicitly separate values, not decimal characters. */
export function formatDigit(digit: bigint, radix: bigint): string {
  requireBigInt(digit, "Digit");
  requireBigInt(radix, "Radix");
  if (radix < 2n || digit < 0n || digit >= radix) throw new RangeError("The digit must be within its radix.");
  if (radix <= 36n) return "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"[Number(digit)]!;
  if (radix === 1000n) return digit.toString().padStart(3, "0");
  return `[${digit}]`;
}
