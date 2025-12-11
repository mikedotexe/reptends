/**
 * Math utilities for reptend analysis
 */

/**
 * Compute base^exp mod m using repeated squaring
 */
export function powMod(base: number, exp: number, mod: number): number {
  if (mod === 1) return 0;
  let result = 1;
  base = base % mod;
  while (exp > 0) {
    if (exp % 2 === 1) {
      result = (result * base) % mod;
    }
    exp = Math.floor(exp / 2);
    base = (base * base) % mod;
  }
  return result;
}

/**
 * Trial division factorization
 * Returns a Map of prime -> exponent
 * Sufficient for numbers up to ~10^12 with small factors
 */
export function factorize(n: number): Map<number, number> {
  const factors = new Map<number, number>();

  // Handle 2 separately
  while (n % 2 === 0) {
    factors.set(2, (factors.get(2) || 0) + 1);
    n = n / 2;
  }

  // Check odd factors up to sqrt(n)
  let i = 3;
  while (i * i <= n) {
    while (n % i === 0) {
      factors.set(i, (factors.get(i) || 0) + 1);
      n = n / i;
    }
    i += 2;
  }

  // If n is still greater than 1, it's a prime factor
  if (n > 1) {
    factors.set(n, 1);
  }

  return factors;
}

/**
 * Get all prime factors as an array (for display)
 */
export function primeFactors(n: number): number[] {
  return Array.from(factorize(n).keys()).sort((a, b) => a - b);
}

/**
 * Format factorization as string (e.g., "2² × 3 × 5")
 */
export function formatFactorization(n: number): string {
  const factors = factorize(n);
  if (factors.size === 0) return '1';

  const superscripts: Record<string, string> = {
    '0': '⁰', '1': '¹', '2': '²', '3': '³', '4': '⁴',
    '5': '⁵', '6': '⁶', '7': '⁷', '8': '⁸', '9': '⁹'
  };

  const toSuperscript = (num: number): string => {
    return num.toString().split('').map(d => superscripts[d]).join('');
  };

  return Array.from(factors.entries())
    .sort(([a], [b]) => a - b)
    .map(([prime, exp]) => exp === 1 ? prime.toString() : `${prime}${toSuperscript(exp)}`)
    .join(' × ');
}

/**
 * Compute multiplicative order of k mod p
 * Returns the smallest positive integer d such that k^d ≡ 1 (mod p)
 * Assumes p is prime and gcd(k, p) = 1
 */
export function multiplicativeOrder(k: number, p: number): number {
  if (k % p === 0) return 0; // k ≡ 0 (mod p), no order

  k = ((k % p) + p) % p; // Normalize k to [0, p)
  if (k === 1) return 1;

  // The order must divide p-1 (Fermat's little theorem)
  const phi = p - 1;

  // Find divisors of phi and check each
  const divisors: number[] = [];
  for (let i = 1; i * i <= phi; i++) {
    if (phi % i === 0) {
      divisors.push(i);
      if (i !== phi / i) {
        divisors.push(phi / i);
      }
    }
  }
  divisors.sort((a, b) => a - b);

  // Find smallest divisor d where k^d ≡ 1 (mod p)
  for (const d of divisors) {
    if (powMod(k, d, p) === 1) {
      return d;
    }
  }

  return phi; // Shouldn't reach here for valid inputs
}

/**
 * Check if k is a QR-generator mod p
 * i.e., ord_p(k) = (p-1)/2
 */
export function isQRGenerator(k: number, p: number): boolean {
  const order = multiplicativeOrder(k, p);
  return order === (p - 1) / 2;
}

/**
 * Check if n is prime (simple trial division)
 */
export function isPrime(n: number): boolean {
  if (n < 2) return false;
  if (n === 2) return true;
  if (n % 2 === 0) return false;
  for (let i = 3; i * i <= n; i += 2) {
    if (n % i === 0) return false;
  }
  return true;
}

/**
 * Compute the reptend (repeating part) of 1/p in base 10
 * Returns the reptend as a string with leading zeros preserved
 */
export function computeReptend(p: number): string {
  if (p <= 1) return '';

  const order = multiplicativeOrder(10, p);
  let remainder = 1;
  let digits = '';

  for (let i = 0; i < order; i++) {
    remainder *= 10;
    digits += Math.floor(remainder / p).toString();
    remainder = remainder % p;
  }

  return digits;
}

/**
 * Analyze a k-family: compute 10^m - k for various m values
 * Returns info about each composite including prime factors and QR-generator status
 */
export interface KFamilyEntry {
  m: number;
  tenPowerM: number;
  composite: number;
  factors: Map<number, number>;
  primes: Array<{
    prime: number;
    isQRGen: boolean;
    order: number;
  }>;
}

export function analyzeKFamily(k: number, maxM: number = 6): KFamilyEntry[] {
  const entries: KFamilyEntry[] = [];

  for (let m = 2; m <= maxM; m++) {
    const tenPowerM = Math.pow(10, m);
    const composite = tenPowerM - k;

    if (composite <= 0) continue;

    const factors = factorize(composite);
    const primes = Array.from(factors.keys())
      .filter(p => p > 1)
      .map(prime => ({
        prime,
        isQRGen: isQRGenerator(k, prime),
        order: multiplicativeOrder(k, prime)
      }));

    entries.push({
      m,
      tenPowerM,
      composite,
      factors,
      primes
    });
  }

  return entries;
}
