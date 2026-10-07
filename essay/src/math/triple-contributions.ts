/**
 * Ordered lattice contributions to (1/(B-1))^3.
 * The three factors each supply B^-i for positive i; their product contributes
 * B^-(i+j+k). Thus plane s has binomial(s-1, 2) unit contributions.
 * These are raw coefficients, not normalized radix words after carrying.
 */
export interface OrderedTriple {
  readonly i: number;
  readonly j: number;
  readonly k: number;
}

export interface TriplePlane {
  /** One-based radix exponent s; positions 1 and 2 have no contributions. */
  readonly place: number;
  readonly points: readonly OrderedTriple[];
  readonly coefficient: bigint;
  /** The base B is supplied separately: each point has weight 1 / B^s. */
  readonly perPointWeight: {
    readonly numerator: 1n;
    readonly radixExponent: number;
  };
}

/** Exact coefficient without enumerating points, even for very large s. */
export function tripleCoefficient(place: bigint): bigint {
  if (typeof place !== "bigint") throw new TypeError("The coefficient place must be a BigInt integer.");
  if (place < 1n) throw new RangeError("The radix place must be positive and one-based.");
  return place < 3n ? 0n : (place - 1n) * (place - 2n) / 2n;
}

/**
 * Enumerate all ordered positive triples on i+j+k=s in lexicographic i,j order.
 * Coordinates are safe bounded integers for direct use by a visual layer.
 * A separate coefficient function avoids enumeration when s exceeds 64.
 */
export function enumerateTriplePlane(place: number): TriplePlane {
  if (!Number.isSafeInteger(place) || place < 1 || place > 64) {
    throw new RangeError("Enumerated radix places must be integers from 1 through 64.");
  }
  const points: OrderedTriple[] = [];
  for (let i = 1; i <= place - 2; i += 1) {
    for (let j = 1; j <= place - i - 1; j += 1) {
      points.push({ i, j, k: place - i - j });
    }
  }
  const coefficient = tripleCoefficient(BigInt(place));
  if (BigInt(points.length) !== coefficient) {
    throw new Error("The enumerated triple plane disagrees with its exact coefficient.");
  }
  return { place, points, coefficient, perPointWeight: { numerator: 1n, radixExponent: place } };
}
