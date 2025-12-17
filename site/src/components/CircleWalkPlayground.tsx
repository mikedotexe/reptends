import React, { useState, useEffect, useCallback } from 'react';

/**
 * Compute multiplicative order of `base` mod `prime`
 * (smallest positive k such that base^k ≡ 1 mod prime)
 */
function multiplicativeOrder(base: number, prime: number): number {
  let current = base % prime;
  let order = 1;
  while (current !== 1 && order < prime) {
    current = (current * base) % prime;
    order++;
  }
  return order;
}

/**
 * Check if n is prime (simple trial division)
 */
function isPrime(n: number): boolean {
  if (n < 2) return false;
  if (n === 2) return true;
  if (n % 2 === 0) return false;
  for (let i = 3; i * i <= n; i += 2) {
    if (n % i === 0) return false;
  }
  return true;
}

/**
 * Modular exponentiation: compute base^exp mod mod
 */
function modPow(base: number, exp: number, mod: number): number {
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
 * Check if x is a quadratic residue mod p
 * Uses Euler's criterion: x^((p-1)/2) ≡ 1 (mod p) iff x is QR
 */
function isQuadraticResidue(x: number, prime: number): boolean {
  if (x % prime === 0) return false;
  const exp = (prime - 1) / 2;
  return modPow(x, exp, prime) === 1;
}

/**
 * Euler's totient function φ(n)
 */
function eulerPhi(n: number): number {
  let result = n;
  let temp = n;
  for (let p = 2; p * p <= temp; p++) {
    if (temp % p === 0) {
      while (temp % p === 0) temp = Math.floor(temp / p);
      result -= Math.floor(result / p);
    }
  }
  if (temp > 1) result -= Math.floor(result / temp);
  return result;
}

/**
 * Generate SVG polygon points for a star shape
 */
function starPoints(cx: number, cy: number, r: number, numPoints = 5): string {
  const innerR = r * 0.5;
  const coords: string[] = [];
  for (let i = 0; i < numPoints * 2; i++) {
    const radius = i % 2 === 0 ? r : innerR;
    const angle = (i * Math.PI) / numPoints - Math.PI / 2;
    coords.push(`${cx + Math.cos(angle) * radius},${cy + Math.sin(angle) * radius}`);
  }
  return coords.join(' ');
}

/**
 * Format a digit for display in the given base.
 * Uses 0-9, then A-Z for bases > 10.
 */
const DIGIT_CHARS = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ';
function formatDigit(d: number): string {
  if (d < 0 || d >= DIGIT_CHARS.length) return '?';
  return DIGIT_CHARS[d];
}

/**
 * Find the antisymmetry index: smallest t where d^t ≡ -1 (mod p)
 * Returns null if no such t exists (d is a quadratic residue)
 */
function findAntisymmetryIndex(d: number, prime: number): number | null {
  let current = d % prime;
  const target = prime - 1; // -1 mod p

  for (let t = 1; t < prime; t++) {
    if (current === target) {
      return t;
    }
    current = (current * d) % prime;
    if (current === 1) {
      // Hit 1 before hitting -1, so -1 is not in the orbit
      return null;
    }
  }
  return null;
}

/**
 * Find the "distance to exponential" - the k and d where B^k ≡ d (mod p)
 * and d is small. This reveals the block structure.
 *
 * Returns { k, d, bPowK } where:
 * - k is the stride (block size)
 * - d is the block multiplier (B^k mod p)
 * - bPowK is B^k (the reference power)
 */
function findBlockStructure(base: number, prime: number): { k: number; d: number; bPowK: number } {
  let bestK = 1;
  let bestD = base % prime;
  let bestBPowK = base;

  let power = base;
  for (let k = 1; k <= 10; k++) {
    const d = power % prime;
    // Consider both d and (prime - d) as "small"
    const effectiveD = Math.min(d, prime - d);

    if (effectiveD < Math.min(bestD, prime - bestD)) {
      bestK = k;
      bestD = d;
      bestBPowK = power;
    }

    power *= base;
    if (power > 1e12) break; // Avoid overflow
  }

  return { k: bestK, d: bestD, bPowK: bestBPowK };
}

interface WalkStep {
  remainder: number;
  digit: number;
}

/**
 * Interactive visualization: "The number IS the point"
 *
 * A rational a/p is a point on a circle of size p-1.
 * The base determines how you walk the circle.
 * The decimal digits are landmarks you pass.
 */
const CircleWalkPlayground = () => {
  const [prime, setPrime] = useState(19);
  const [numerator, setNumerator] = useState(1);
  const [base, setBase] = useState(10);
  const [step, setStep] = useState(0);
  const [isPlaying, setIsPlaying] = useState(false);
  const [speed, setSpeed] = useState(800);
  const [customPrime, setCustomPrime] = useState('');
  const [customBase, setCustomBase] = useState('');
  const [showBlockLayer, setShowBlockLayer] = useState(false);
  const [showCosetComparison, setShowCosetComparison] = useState(false);

  // Compute the full walk
  const computeWalk = useCallback((): WalkStep[] => {
    const walk: WalkStep[] = [];
    let current = numerator % prime;
    const seen = new Set<number>();

    while (!seen.has(current) && walk.length < prime) {
      seen.add(current);
      const product = current * base;
      const digit = Math.floor(product / prime);
      const next = product % prime;
      walk.push({ remainder: current, digit });
      current = next;
    }

    return walk;
  }, [prime, numerator, base]);

  const walk = computeWalk();
  const period = multiplicativeOrder(base, prime);
  const currentRemainder = step < walk.length ? walk[step].remainder : walk[0]?.remainder;

  // Block structure: the "two gears" - fast (×B) and slow (×d)
  const blockStructure = findBlockStructure(base, prime);
  const { k: blockSize, d: blockMultiplier, bPowK } = blockStructure;

  // Block orbit order: how many block-steps to return (d^m ≡ 1)
  const blockOrder = multiplicativeOrder(blockMultiplier, prime);

  // Antisymmetry: find t where d^t ≡ -1 (if it exists)
  const antisymmetryIndex = findAntisymmetryIndex(blockMultiplier, prime);
  const hasAntisymmetry = antisymmetryIndex !== null;

  // Compute the complete block orbit (all positions the slow gear visits)
  const computeFullBlockOrbit = () => {
    const orbit: number[] = [numerator % prime];
    let current = numerator % prime;
    for (let i = 1; i < blockOrder; i++) {
      current = (current * blockMultiplier) % prime;
      orbit.push(current);
    }
    return orbit;
  };
  const fullBlockOrbit = computeFullBlockOrbit();

  // QR Layer: quadratic residue analysis
  const qrCount = (prime - 1) / 2;
  const primitiveRootCount = eulerPhi(prime - 1);
  const baseIsQR = isQuadraticResidue(base, prime);
  const baseIsPrimitive = multiplicativeOrder(base, prime) === prime - 1;

  // Coset analysis: numerator determines which coset the orbit lives in
  const numeratorIsQR = isQuadraticResidue(numerator, prime);
  const blockMultiplierIsQR = isQuadraticResidue(blockMultiplier, prime);
  // When d is QR: orbit stays in numerator's coset. When d is NQR: orbit alternates!
  const orbitStaysInCoset = blockMultiplierIsQR;

  // Find a contrasting numerator for comparison (opposite coset)
  const contrastingNumerator = (() => {
    // Find smallest number in opposite coset
    for (let n = 1; n < prime; n++) {
      const nIsQR = isQuadraticResidue(n, prime);
      if (nIsQR !== numeratorIsQR) return n;
    }
    return numeratorIsQR ? 2 : 1; // fallback
  })();


  // Compute block-start remainders for geometric progression display
  const computeBlockStartRemainders = () => {
    const remainders: { r: number; isQR: boolean }[] = [];
    let r = numerator % prime;
    const seen = new Set<number>();
    for (let i = 0; i < Math.min(blockOrder, 12); i++) {
      if (seen.has(r)) break;
      seen.add(r);
      remainders.push({ r, isQR: isQuadraticResidue(r, prime) });
      r = (r * blockMultiplier) % prime;
    }
    return remainders;
  };
  const blockStartRemainders = computeBlockStartRemainders();

  // Animation effect with auto-reset on orbit complete
  useEffect(() => {
    if (!isPlaying) return;

    const timer = setInterval(() => {
      setStep((s) => {
        if (s >= walk.length - 1) {
          // Stop playback and immediately reset to step 0
          setIsPlaying(false);
          return 0;
        }
        return s + 1;
      });
    }, speed);

    return () => clearInterval(timer);
  }, [isPlaying, speed, walk.length]);

  // Reset step when parameters change
  useEffect(() => {
    setStep(0);
    setIsPlaying(false);
  }, [prime, numerator, base]);

  const handlePrimeChange = (p: number) => {
    if (isPrime(p) && p > 2 && p < 500) {
      setPrime(p);
      // Adjust numerator if needed
      if (numerator >= p) setNumerator(1);
    }
  };

  const handleCustomPrime = () => {
    const p = parseInt(customPrime);
    if (isPrime(p) && p > 2 && p < 500) {
      setPrime(p);
      if (numerator >= p) setNumerator(1);
      setCustomPrime('');
    }
  };

  const handleCustomBase = () => {
    const b = parseInt(customBase);
    if (b >= 2 && b < 100) {
      setBase(b);
      setCustomBase('');
    }
  };

  // Position calculation for SVG
  const getPosition = (residue: number, radius = 85) => {
    // Place residues evenly around circle
    // Map residue (1 to p-1) to angle
    const index = residue - 1; // 0-indexed
    const total = prime - 1;
    const angle = (index / total) * 2 * Math.PI - Math.PI / 2;
    return {
      x: 100 + Math.cos(angle) * radius,
      y: 100 + Math.sin(angle) * radius,
    };
  };

  // Build path through visited remainders
  const visitedRemainders = walk.slice(0, step + 1).map((w) => w.remainder);
  const pathPoints = visitedRemainders.map((r) => getPosition(r));
  const pathD =
    pathPoints.length > 1
      ? `M ${pathPoints[0].x} ${pathPoints[0].y} ` +
        pathPoints.slice(1).map((pt) => `L ${pt.x} ${pt.y}`).join(' ')
      : '';

  // Digits accumulated so far
  const digits = walk.slice(0, step + 1).map((w) => w.digit);
  const digitString = digits.length > 0
    ? '0.' + digits.map(d => formatDigit(d)).join('')
    : '0.';

  const commonPrimes = [7, 19, 97];
  const commonBases = [2, 7, 10, 12];

  return (
    <div className="bg-stone-100 rounded-lg p-4 sm:p-6 border border-stone-200">
      <div className="grid grid-cols-1 lg:grid-cols-2 gap-6">
        {/* Left: Circle visualization */}
        <div className="flex flex-col items-center">
          {/* Coset Comparison View - two circles side by side */}
          {showCosetComparison && (
            <div className="flex flex-col items-center">
              <div className="text-xs font-semibold text-stone-600 mb-2 text-center">
                Two Cosets, Same Structure
              </div>
              <div className="flex gap-2">
                {/* QR Coset Circle */}
                {[
                  { num: numeratorIsQR ? numerator : contrastingNumerator, isQR: true, label: 'QR Coset' },
                  { num: numeratorIsQR ? contrastingNumerator : numerator, isQR: false, label: 'NQR Coset' },
                ].map(({ num, isQR, label }) => {
                  // Compute walk for this numerator
                  const thisWalk: WalkStep[] = [];
                  let current = num % prime;
                  const seen = new Set<number>();
                  while (!seen.has(current) && thisWalk.length < prime) {
                    seen.add(current);
                    const product = current * base;
                    const digit = Math.floor(product / prime);
                    const next = product % prime;
                    thisWalk.push({ remainder: current, digit });
                    current = next;
                  }
                  const thisVisited = thisWalk.slice(0, step + 1).map(w => w.remainder);
                  const thisDigits = thisWalk.slice(0, step + 1).map(w => w.digit);
                  const thisCurrent = step < thisWalk.length ? thisWalk[step].remainder : thisWalk[0]?.remainder;

                  return (
                    <div key={num} className="flex flex-col items-center">
                      <svg viewBox="0 0 120 120" className="w-28 h-28 sm:w-32 sm:h-32">
                        <circle cx="60" cy="60" r="50" fill="none" stroke="#d6d3d1" strokeWidth="1" />
                        {/* Points */}
                        {Array.from({ length: prime - 1 }, (_, i) => i + 1).map((r) => {
                          const rIsQR = isQuadraticResidue(r, prime);
                          const inThisCoset = rIsQR === isQR;
                          const angle = ((r - 1) / (prime - 1)) * 2 * Math.PI - Math.PI / 2;
                          const px = 60 + Math.cos(angle) * 45;
                          const py = 60 + Math.sin(angle) * 45;
                          const isVisited = thisVisited.includes(r);
                          const isCurrent = r === thisCurrent;

                          if (!inThisCoset) {
                            // Opposite coset: tiny faint dot
                            return (
                              <circle key={r} cx={px} cy={py} r={2} fill="#e5e5e5" />
                            );
                          }

                          const fillColor = isCurrent
                            ? '#10b981'
                            : isVisited
                            ? (isQR ? '#c4b5fd' : '#fecaca')
                            : (isQR ? '#ede9fe' : '#fee2e2');

                          return isQR ? (
                            <polygon
                              key={r}
                              points={starPoints(px, py, isCurrent ? 8 : isVisited ? 6 : 4, 5)}
                              fill={fillColor}
                              className="transition-all duration-200"
                            />
                          ) : (
                            <circle
                              key={r}
                              cx={px}
                              cy={py}
                              r={isCurrent ? 8 : isVisited ? 6 : 4}
                              fill={fillColor}
                              className="transition-all duration-200"
                            />
                          );
                        })}
                        {/* Center label */}
                        <text x="60" y="60" textAnchor="middle" dominantBaseline="middle"
                          className={`text-[8px] font-mono ${isQR ? 'fill-violet-600' : 'fill-rose-600'}`}>
                          {num}/{prime}
                        </text>
                      </svg>
                      {/* Digit strip */}
                      <div className={`text-[10px] font-mono px-2 py-1 rounded mt-1 ${
                        isQR ? 'bg-violet-100 text-violet-800' : 'bg-rose-100 text-rose-800'
                      }`}>
                        0.{thisDigits.slice(0, 6).map(d => formatDigit(d)).join('')}{thisDigits.length > 6 ? '...' : ''}
                      </div>
                      <div className={`text-[9px] mt-1 font-semibold ${
                        isQR ? 'text-violet-600' : 'text-rose-600'
                      }`}>
                        {label}
                      </div>
                    </div>
                  );
                })}
              </div>
              <div className="text-[10px] text-stone-500 mt-3 text-center max-w-xs">
                Both orbits have identical structure — the numerator just selects which half of the group you traverse.
              </div>
            </div>
          )}

          {/* Default View - flat circle with digit display */}
          {!showBlockLayer && !showCosetComparison && (
            <div className="flex flex-col items-center">
              {/* Circle container */}
              <div className="mb-2">
                <svg
                  viewBox="0 0 200 200"
                  className="w-56 h-56 sm:w-64 sm:h-64"
                >
                  {/* Outer circle */}
                  <circle
                    cx="100"
                    cy="100"
                    r="90"
                    fill="none"
                    stroke="#d6d3d1"
                    strokeWidth="1"
                  />

                  {/* All residue points - QRs as stars, NQRs as circles */}
                  {Array.from({ length: prime - 1 }, (_, i) => i + 1).map((r) => {
                    const pos = getPosition(r, 80);
                    const isQR = isQuadraticResidue(r, prime);
                    const isVisited = visitedRemainders.includes(r);
                    const isCurrent = r === currentRemainder;
                    const isStart = r === numerator;

                    const pointRadius = isCurrent ? 12 : isVisited ? 10 : 8;
                    const fillColor = isCurrent
                      ? '#10b981'
                      : isVisited
                      ? '#6ee7b7'
                      : isStart
                      ? '#fbbf24'
                      : isQR
                      ? '#c4b5fd'
                      : '#fecaca';

                    return (
                      <g key={r}>
                        {isQR ? (
                          <polygon
                            points={starPoints(pos.x, pos.y, pointRadius, 5)}
                            fill={fillColor}
                            className="transition-all duration-200"
                          />
                        ) : (
                          <circle
                            cx={pos.x}
                            cy={pos.y}
                            r={pointRadius}
                            fill={fillColor}
                            className="transition-all duration-200"
                          />
                        )}
                      </g>
                    );
                  })}

                  {/* Path trace */}
                  {pathD && (
                    <path
                      d={pathD}
                      fill="none"
                      stroke="#10b981"
                      strokeWidth="2"
                      strokeLinecap="round"
                      strokeLinejoin="round"
                      style={{ opacity: 0.5 }}
                    />
                  )}

                  {/* Center label */}
                  <text
                    x="100"
                    y="100"
                    textAnchor="middle"
                    dominantBaseline="middle"
                    className="text-[10px] font-mono fill-stone-400"
                  >
                    (ℤ/{prime}ℤ)*
                  </text>
                </svg>
              </div>

              {/* Digit strip - grouped by blockSize */}
              <div className="bg-stone-50 rounded-lg px-3 py-2 border border-stone-200 shadow-sm">
                <div className="flex font-mono text-base sm:text-lg tracking-wider justify-center flex-wrap">
                  <span className="text-stone-400">0.</span>
                  {blockSize > 1 ? (
                    // Group digits into blocks
                    <>
                      {Array.from({ length: Math.ceil(digits.length / blockSize) }, (_, bi) => {
                        const blockDigits = digits.slice(bi * blockSize, (bi + 1) * blockSize);
                        const blockStart = bi * blockSize;
                        return (
                          <span key={bi} className="mr-1">
                            {blockDigits.map((d, di) => {
                              const globalIndex = blockStart + di;
                              return (
                                <span
                                  key={di}
                                  className={`transition-all duration-200 ${
                                    globalIndex === step
                                      ? 'text-emerald-600 font-bold scale-110'
                                      : 'text-stone-600'
                                  }`}
                                >
                                  {formatDigit(d)}
                                </span>
                              );
                            })}
                          </span>
                        );
                      })}
                    </>
                  ) : (
                    // No grouping for blockSize 1
                    digits.map((d, i) => (
                      <span
                        key={i}
                        className={`transition-all duration-200 ${
                          i === step
                            ? 'text-emerald-600 font-bold scale-110'
                            : 'text-stone-600'
                        }`}
                      >
                        {formatDigit(d)}
                      </span>
                    ))
                  )}
                  {step < walk.length - 1 && (
                    <span className="text-stone-300 animate-pulse">_</span>
                  )}
                </div>
              </div>

              {/* Fraction display */}
              <div className="mt-2 text-sm font-mono text-stone-600">
                {numerator}/{prime}
              </div>

              {/* Legend */}
              <div className="mt-4 bg-stone-50 rounded-lg p-3 border border-stone-200">
                <div className="text-[10px] font-semibold text-stone-600 mb-2">Legend</div>
                <div className="grid grid-cols-2 gap-x-4 gap-y-1 text-[10px] sm:text-xs">
                  <div className="flex items-center gap-2">
                    <svg viewBox="0 0 16 16" className="w-4 h-4">
                      <polygon points={starPoints(8, 8, 6, 5)} fill="#c4b5fd" />
                    </svg>
                    <span className="text-stone-600">QR (quadratic residue)</span>
                  </div>
                  <div className="flex items-center gap-2">
                    <span className="w-3 h-3 rounded-full bg-rose-300"></span>
                    <span className="text-stone-600">NQR (non-residue)</span>
                  </div>
                  <div className="flex items-center gap-2">
                    <svg viewBox="0 0 16 16" className="w-4 h-4">
                      <polygon points={starPoints(8, 8, 6, 5)} fill="#10b981" />
                    </svg>
                    <span className="text-stone-600">current position</span>
                  </div>
                  <div className="flex items-center gap-2">
                    <span className="w-3 h-3 rounded-full bg-emerald-300"></span>
                    <span className="text-stone-600">visited</span>
                  </div>
                </div>
              </div>
            </div>
          )}

          {/* Block Layer View - flat circle with block structure overlays */}
          {showBlockLayer && !showCosetComparison && (
          <>
          <svg viewBox="0 0 200 200" className="w-56 h-56 sm:w-64 sm:h-64">
            {/* Outer circle */}
            <circle
              cx="100"
              cy="100"
              r="90"
              fill="none"
              stroke="#d6d3d1"
              strokeWidth="1"
            />

            {/* All residue points - QRs as stars, NQRs as circles */}
            {Array.from({ length: prime - 1 }, (_, i) => i + 1).map((r) => {
              const pos = getPosition(r, 80); // Slightly smaller orbit for bigger points
              const isQR = isQuadraticResidue(r, prime);
              const isPrimRoot = multiplicativeOrder(r, prime) === prime - 1;
              const isVisited = visitedRemainders.includes(r);
              const isCurrent = r === currentRemainder;
              const isStart = r === numerator;

              // Find digit emitted when visiting this remainder
              const visitedIndex = visitedRemainders.indexOf(r);
              const digitAtThisPoint = visitedIndex >= 0 && visitedIndex < walk.length
                ? walk[visitedIndex].digit
                : undefined;

              // Point size
              const pointRadius = isCurrent ? 12 : isVisited ? 10 : 8;

              // Colors: visited/current override QR colors
              const fillColor = isCurrent
                ? '#10b981'
                : isVisited
                ? '#6ee7b7'
                : isStart
                ? '#fbbf24'
                : isQR
                ? '#c4b5fd'
                : '#fecaca';

              // Gold border for primitive roots
              const strokeColor = isPrimRoot ? '#f59e0b' : 'none';
              const strokeWidth = isPrimRoot ? 2 : 0;

              return (
                <g key={r}>
                  {/* Shape: star for QR, circle for NQR */}
                  {isQR ? (
                    <polygon
                      points={starPoints(pos.x, pos.y, pointRadius, 5)}
                      fill={fillColor}
                      stroke={strokeColor}
                      strokeWidth={strokeWidth}
                      className="transition-all duration-200"
                    />
                  ) : (
                    <circle
                      cx={pos.x}
                      cy={pos.y}
                      r={pointRadius}
                      fill={fillColor}
                      stroke={strokeColor}
                      strokeWidth={strokeWidth}
                      className="transition-all duration-200"
                    />
                  )}
                  {/* Digit INSIDE the point (for visited) */}
                  {isVisited && digitAtThisPoint !== undefined && (
                    <text
                      x={pos.x}
                      y={pos.y + 1}
                      textAnchor="middle"
                      dominantBaseline="middle"
                      className="text-[8px] font-mono font-bold fill-stone-800"
                      style={{ pointerEvents: 'none' }}
                    >
                      {formatDigit(digitAtThisPoint)}
                    </text>
                  )}
                  {/* Residue label OUTSIDE (radially) */}
                  {(prime <= 23 || isVisited || isStart) && (
                    <text
                      x={pos.x + (pos.x > 100 ? 16 : -16)}
                      y={pos.y}
                      textAnchor={pos.x > 100 ? 'start' : 'end'}
                      dominantBaseline="middle"
                      className={`text-[7px] font-mono transition-all duration-200 ${
                        isCurrent
                          ? 'fill-emerald-700 font-bold'
                          : isVisited
                          ? 'fill-emerald-600'
                          : isStart
                          ? 'fill-amber-600 font-bold'
                          : 'fill-stone-400'
                      }`}
                    >
                      {r}
                    </text>
                  )}
                </g>
              );
            })}

            {/* Path trace (only in single-walker mode, not in block layer) */}
            {!showBlockLayer && pathD && (
              <path
                d={pathD}
                fill="none"
                stroke="#10b981"
                strokeWidth="2"
                strokeLinecap="round"
                strokeLinejoin="round"
                className="transition-all duration-300"
                style={{ opacity: 0.5 }}
              />
            )}

            {/* Block layer: fine path (muted) */}
            {showBlockLayer && pathD && (
              <path
                d={pathD}
                fill="none"
                stroke="#a8a29e"
                strokeWidth="1"
                strokeLinecap="round"
                strokeLinejoin="round"
                strokeDasharray="2,2"
                style={{ opacity: 0.4 }}
              />
            )}

            {/* Block layer: complete polygon preview (faint) */}
            {showBlockLayer && fullBlockOrbit.length >= 3 && (() => {
              const polygonPoints = fullBlockOrbit.map(r => getPosition(r));
              const polygonD = `M ${polygonPoints[0].x} ${polygonPoints[0].y} ` +
                polygonPoints.slice(1).map(pt => `L ${pt.x} ${pt.y}`).join(' ') + ' Z';

              return (
                <path
                  d={polygonD}
                  fill="none"
                  stroke="#fca5a5"
                  strokeWidth="1"
                  strokeDasharray="4,4"
                  className="transition-all duration-300"
                  style={{ opacity: 0.4 }}
                />
              );
            })()}

            {/* Block layer: antisymmetry lines (connecting r to p-r) */}
            {showBlockLayer && hasAntisymmetry && (() => {
              // Find pairs in the visited block orbit that are antipodal
              const visitedBlocks = visitedRemainders.filter((_, i) => i % blockSize === 0);
              const antipodalLines: React.ReactElement[] = [];

              visitedBlocks.forEach((r, idx) => {
                const opposite = prime - r;
                const oppositeIdx = visitedBlocks.indexOf(opposite);
                if (oppositeIdx > idx) {
                  const pos1 = getPosition(r);
                  const pos2 = getPosition(opposite);
                  antipodalLines.push(
                    <line
                      key={`anti-${r}-${opposite}`}
                      x1={pos1.x}
                      y1={pos1.y}
                      x2={pos2.x}
                      y2={pos2.y}
                      stroke="#8b5cf6"
                      strokeWidth="2"
                      strokeDasharray="3,3"
                      style={{ opacity: 0.6 }}
                    />
                  );
                }
              });

              return antipodalLines;
            })()}

            {/* Block layer: block orbit chords (bold) */}
            {showBlockLayer && (() => {
              // Get block positions visited so far
              const blockPositions = visitedRemainders.filter((_, i) => i % blockSize === 0);
              if (blockPositions.length < 2) return null;

              const blockPoints = blockPositions.map(r => getPosition(r));
              const blockPathD = `M ${blockPoints[0].x} ${blockPoints[0].y} ` +
                blockPoints.slice(1).map(pt => `L ${pt.x} ${pt.y}`).join(' ');

              return (
                <path
                  d={blockPathD}
                  fill="none"
                  stroke="#dc2626"
                  strokeWidth="3"
                  strokeLinecap="round"
                  strokeLinejoin="round"
                  className="transition-all duration-300"
                  style={{ opacity: 0.7 }}
                />
              );
            })()}

            {/* Block layer: highlight block orbit points */}
            {showBlockLayer && visitedRemainders.map((r, i) => {
              if (i % blockSize !== 0) return null;
              const pos = getPosition(r);
              const isCurrentBlock = Math.floor(step / blockSize) === Math.floor(i / blockSize);
              return (
                <g key={`block-${i}`}>
                  <circle
                    cx={pos.x}
                    cy={pos.y}
                    r={isCurrentBlock ? 10 : 7}
                    fill={isCurrentBlock ? '#dc2626' : '#fca5a5'}
                    stroke="#991b1b"
                    strokeWidth="2"
                    className="transition-all duration-200"
                  />
                  <text
                    x={pos.x}
                    y={pos.y + 1}
                    textAnchor="middle"
                    dominantBaseline="middle"
                    className="text-[7px] font-mono font-bold fill-white"
                  >
                    {Math.floor(i / blockSize)}
                  </text>
                </g>
              );
            })}

            {/* Current position pulse (single-walker mode only) */}
            {step > 0 && currentRemainder && (
              <circle
                cx={getPosition(currentRemainder).x}
                cy={getPosition(currentRemainder).y}
                r="12"
                fill="none"
                stroke="#10b981"
                strokeWidth="2"
                className="animate-pulse"
                style={{ opacity: 0.5 }}
              />
            )}

            {/* Center label */}
            <text
              x="100"
              y="96"
              textAnchor="middle"
              dominantBaseline="middle"
              className="text-[10px] sm:text-xs font-mono fill-stone-500"
            >
              (ℤ/{prime}ℤ)*
            </text>
            <text
              x="100"
              y="108"
              textAnchor="middle"
              dominantBaseline="middle"
              className="text-[9px] font-mono fill-stone-400"
            >
              base {base}
            </text>
          </svg>

          {/* Path display */}
          <div className="mt-3 text-center max-w-xs">
            <div className="text-[10px] sm:text-xs font-mono text-stone-500 mb-1">
              Path: {visitedRemainders.slice(0, 8).join(' → ')}{visitedRemainders.length > 8 ? ' → ...' : ''}
            </div>
            <div className="text-sm sm:text-base font-mono text-stone-800 font-semibold">
              {numerator}/{prime} = {digitString}{step < walk.length - 1 ? '...' : ''}
            </div>
          </div>

          {/* Legend */}
          {showBlockLayer ? (
            <div className="text-[9px] sm:text-[10px] font-mono text-stone-500 mt-3 flex flex-wrap gap-3">
              <span className="inline-flex items-center gap-1">
                <span className="w-3 h-0.5 bg-rose-500"></span>
                block path
              </span>
              <span className="inline-flex items-center gap-1">
                <span className="w-3 h-0.5 bg-rose-300" style={{ borderBottom: '1px dashed' }}></span>
                {blockOrder}-gon
              </span>
              {hasAntisymmetry && (
                <span className="inline-flex items-center gap-1">
                  <span className="w-3 h-0.5 bg-violet-500" style={{ borderBottom: '1px dashed' }}></span>
                  antipodal
                </span>
              )}
            </div>
          ) : (
            <div className="text-[9px] sm:text-[10px] font-mono text-stone-500 mt-3 flex flex-wrap gap-3">
              <span className="inline-flex items-center gap-1">
                <span className="text-violet-400">★</span>
                QR
              </span>
              <span className="inline-flex items-center gap-1">
                <span className="w-2 h-2 rounded-full bg-rose-300"></span>
                NQR
              </span>
              <span className="inline-flex items-center gap-1">
                <span className="w-2 h-2 rounded-full border-2 border-amber-500 bg-transparent"></span>
                primitive
              </span>
              <span className="inline-flex items-center gap-1">
                <span className="w-2 h-2 rounded-full bg-emerald-500"></span>
                current
              </span>
            </div>
          )}
          </>
          )}
        </div>

        {/* Right: Controls */}
        <div className="space-y-4">
          {/* Prime selector */}
          <div>
            <label className="block text-xs font-semibold text-stone-600 mb-2">
              Prime (the circle)
            </label>
            <div className="flex flex-wrap gap-2 mb-2">
              {commonPrimes.map((p) => (
                <button
                  key={p}
                  onClick={() => handlePrimeChange(p)}
                  className={`px-3 py-1 text-sm font-mono rounded transition-colors ${
                    prime === p
                      ? 'bg-stone-800 text-white'
                      : 'bg-stone-200 text-stone-700 hover:bg-stone-300'
                  }`}
                >
                  {p}
                </button>
              ))}
              <div className="flex gap-1">
                <input
                  type="number"
                  placeholder="custom"
                  value={customPrime}
                  onChange={(e) => setCustomPrime(e.target.value)}
                  onKeyDown={(e) => e.key === 'Enter' && handleCustomPrime()}
                  className="w-16 px-2 py-1 text-sm font-mono border border-stone-300 rounded"
                />
                <button
                  onClick={handleCustomPrime}
                  className="px-2 py-1 text-sm bg-stone-200 rounded hover:bg-stone-300"
                >
                  →
                </button>
              </div>
            </div>
          </div>

          {/* Numerator slider */}
          <div>
            <label className="block text-xs font-semibold text-stone-600 mb-2">
              Numerator (starting point): <span className="text-emerald-600">{numerator}</span>
              <span className={`ml-2 px-1.5 py-0.5 text-[10px] rounded ${
                numeratorIsQR ? 'bg-violet-200 text-violet-800' : 'bg-rose-200 text-rose-800'
              }`}>
                {numeratorIsQR ? 'QR' : 'NQR'}
              </span>
            </label>
            <input
              type="range"
              min={1}
              max={prime - 1}
              value={numerator}
              onChange={(e) => setNumerator(parseInt(e.target.value))}
              className="w-full accent-emerald-600"
            />
            <div className="text-[10px] text-stone-500 mt-1">
              {numeratorIsQR
                ? 'Orbit visits only quadratic residues (★ points)'
                : 'Orbit visits only non-residues (● points)'}
            </div>
          </div>

          {/* Base selector */}
          <div>
            <label className="block text-xs font-semibold text-stone-600 mb-2">
              Base (step size)
            </label>
            <div className="flex flex-wrap gap-2 mb-2">
              {commonBases.map((b) => (
                <button
                  key={b}
                  onClick={() => setBase(b)}
                  className={`px-3 py-1 text-sm font-mono rounded transition-colors ${
                    base === b
                      ? 'bg-stone-800 text-white'
                      : 'bg-stone-200 text-stone-700 hover:bg-stone-300'
                  }`}
                >
                  {b}
                </button>
              ))}
              <div className="flex gap-1">
                <input
                  type="number"
                  placeholder="custom"
                  value={customBase}
                  onChange={(e) => setCustomBase(e.target.value)}
                  onKeyDown={(e) => e.key === 'Enter' && handleCustomBase()}
                  className="w-16 px-2 py-1 text-sm font-mono border border-stone-300 rounded"
                />
                <button
                  onClick={handleCustomBase}
                  className="px-2 py-1 text-sm bg-stone-200 rounded hover:bg-stone-300"
                >
                  →
                </button>
              </div>
            </div>
          </div>

          {/* Animation controls */}
          <div>
            <label className="block text-xs font-semibold text-stone-600 mb-2">
              Animation
            </label>
            <div className="flex gap-2 mb-3 flex-wrap">
              <button
                onClick={() => setStep((s) => Math.max(s - 1, 0))}
                disabled={step <= 0}
                className="px-3 py-2 text-sm font-semibold bg-stone-200 text-stone-700 rounded hover:bg-stone-300 disabled:opacity-50 disabled:cursor-not-allowed"
              >
                ⏮ Back
              </button>
              <button
                onClick={() => setIsPlaying(!isPlaying)}
                className={`px-4 py-2 text-sm font-semibold rounded transition-colors ${
                  isPlaying
                    ? 'bg-amber-500 text-white hover:bg-amber-600'
                    : 'bg-emerald-600 text-white hover:bg-emerald-700'
                }`}
              >
                {isPlaying ? '⏸ Pause' : '▶ Play'}
              </button>
              <button
                onClick={() => setStep((s) => Math.min(s + 1, walk.length - 1))}
                disabled={step >= walk.length - 1}
                className="px-3 py-2 text-sm font-semibold bg-stone-200 text-stone-700 rounded hover:bg-stone-300 disabled:opacity-50 disabled:cursor-not-allowed"
              >
                ⏭ Step
              </button>
              <button
                onClick={() => { setStep(0); setIsPlaying(false); }}
                className="px-3 py-2 text-sm font-semibold bg-stone-200 text-stone-700 rounded hover:bg-stone-300"
              >
                ↺ Reset
              </button>
            </div>

            {/* Speed slider */}
            <div className="flex items-center gap-2">
              <span className="text-[10px] text-stone-500">slow</span>
              <input
                type="range"
                min={200}
                max={2000}
                value={2200 - speed}
                onChange={(e) => setSpeed(2200 - parseInt(e.target.value))}
                className="flex-1 accent-stone-600"
              />
              <span className="text-[10px] text-stone-500">fast</span>
            </div>
          </div>

          {/* Status */}
          <div className="bg-stone-200 rounded p-3 text-xs sm:text-sm font-mono">
            <div className="flex justify-between">
              <span className="text-stone-600">Period:</span>
              <span className="text-stone-800 font-semibold">{period} steps</span>
            </div>
            <div className="flex justify-between">
              <span className="text-stone-600">Current step:</span>
              <span className="text-stone-800">{step + 1} / {walk.length}</span>
            </div>
            <div className="flex justify-between">
              <span className="text-stone-600">ord<sub>{prime}</sub>({base}):</span>
              <span className="text-stone-800">{period}</span>
            </div>
            {/* QR info - always visible */}
            <div className="mt-3 pt-3 border-t border-stone-300 space-y-1">
              <div className="flex justify-between">
                <span className="text-stone-600">Base {base}:</span>
                <span className={baseIsQR ? 'text-violet-600' : 'text-rose-600'}>
                  {baseIsPrimitive ? 'primitive root' : baseIsQR ? 'QR' : 'NQR'}
                </span>
              </div>
              <div className="flex justify-between">
                <span className="text-stone-600">QRs / NQRs:</span>
                <span className="text-stone-700">{qrCount} / {qrCount}</span>
              </div>
            </div>
            {/* Block progress - shown in block layer mode */}
            {showBlockLayer && (
              <div className="mt-3 pt-3 border-t border-stone-300 space-y-1">
                <div className="flex justify-between">
                  <span className="text-amber-700">Block progress:</span>
                  <span className="text-amber-800 font-semibold">
                    {Math.floor((step + 1) / blockSize)} / {blockOrder}
                  </span>
                </div>
                <div className="flex justify-between">
                  <span className="text-amber-700">Block size (k):</span>
                  <span className="text-amber-800">{blockSize} digits</span>
                </div>
              </div>
            )}
          </div>

          {/* QR/NQR Explainer - always visible */}
          <div className="bg-fuchsia-50 border border-fuchsia-200 rounded-lg p-3 text-xs">
            <div className="font-semibold text-fuchsia-800 mb-2">Quadratic Residues</div>
            <p className="text-fuchsia-700 leading-relaxed mb-2">
              The squaring map x → x² is 2-to-1 (since x² = (−x)²), so exactly half
              the circle are squares.
            </p>
            <div className="grid grid-cols-2 gap-2 mb-2">
              <div className="bg-violet-100/50 rounded p-2 border border-violet-200">
                <div className="font-semibold text-violet-800">★ QRs</div>
                <div className="text-violet-600 text-[10px]">{qrCount} squares</div>
              </div>
              <div className="bg-rose-100/50 rounded p-2 border border-rose-200">
                <div className="font-semibold text-rose-800">● NQRs</div>
                <div className="text-rose-600 text-[10px]">{qrCount} non-squares</div>
              </div>
            </div>
            <div className="text-fuchsia-600 text-[10px] border-t border-fuchsia-200 pt-2">
              <span className="text-amber-500 font-bold">★</span> with gold border = primitive root
              (generates full group). There are {primitiveRootCount} of them.
            </div>
          </div>

          {/* View mode toggles */}
          <div className="mt-4 space-y-2">
            {/* Coset Comparison toggle */}
            <button
              onClick={() => {
                setShowCosetComparison(!showCosetComparison);
                if (!showCosetComparison) {
                  setShowBlockLayer(false);
                }
              }}
              className={`w-full px-4 py-2 text-sm font-semibold rounded transition-colors ${
                showCosetComparison
                  ? 'bg-fuchsia-600 text-white hover:bg-fuchsia-700'
                  : 'bg-stone-200 text-stone-700 hover:bg-stone-300'
              }`}
            >
              {showCosetComparison ? '◉ Coset Comparison' : '○ Coset Comparison'}
            </button>

            {/* Block Layer toggle */}
            <button
              onClick={() => {
                setShowBlockLayer(!showBlockLayer);
                if (!showBlockLayer) {
                  setShowCosetComparison(false);
                }
              }}
              className={`w-full px-4 py-2 text-sm font-semibold rounded transition-colors ${
                showBlockLayer
                  ? 'bg-amber-600 text-white hover:bg-amber-700'
                  : 'bg-stone-200 text-stone-700 hover:bg-stone-300'
              }`}
            >
              {showBlockLayer ? '◉ Block Layer (Two Gears)' : '○ Block Layer (Two Gears)'}
            </button>

            {showBlockLayer && (
              <p className="text-[10px] text-stone-500 mt-2 leading-relaxed">
                <span className="text-amber-700 font-semibold">Fast gear:</span> ×{base} (one digit).{' '}
                <span className="text-rose-700 font-semibold">Slow gear:</span> ×{blockMultiplier} (every {blockSize} digits).
              </p>
            )}
          </div>

        </div>
      </div>

      {/* Block layer explainer - full width */}
      {showBlockLayer && (
        <div className="mt-4 bg-amber-50 border border-amber-200 rounded-lg p-4 sm:p-5">
          <div className="font-semibold text-amber-800 mb-3 text-sm sm:text-base">
            The Two Gears
          </div>

          {/* Gap meter visualization */}
          <div className="mb-4">
            <div className="text-xs text-amber-700 mb-2">The Block Multiplier:</div>
            <div className="flex items-center gap-2 flex-wrap font-mono text-sm">
              <span className="text-blue-700">{base}<sup>{blockSize}</sup></span>
              <span className="text-stone-400">=</span>
              <span className="font-bold">{bPowK}</span>
              <span className="text-stone-400">≡</span>
              <span className="text-rose-600 font-bold text-lg">{blockMultiplier}</span>
              <span className="text-stone-500">(mod {prime})</span>
            </div>
            {/* Gap quality: show d as percentage of p */}
            {(() => {
              const gapRatio = blockMultiplier / prime;
              const gapPercent = (gapRatio * 100).toFixed(1);
              const isSweet = gapRatio < 0.1;
              const gap = bPowK - prime;
              const isExactlyBelow = gap === blockMultiplier && gap > 0;

              return (
                <>
                  {/* Visual: show d relative to p */}
                  <div className="mt-2 relative h-6 bg-stone-200 rounded overflow-hidden">
                    <div
                      className={`absolute left-0 top-0 h-full ${isSweet ? 'bg-emerald-400' : 'bg-rose-400'}`}
                      style={{ width: `${Math.min(gapRatio * 100, 100)}%` }}
                    />
                    <div className="absolute inset-0 flex items-center px-2 text-[10px] font-mono">
                      <span className={`font-bold ${isSweet ? 'text-emerald-900' : 'text-rose-900'}`}>
                        d = {blockMultiplier}
                      </span>
                      <span className="flex-1"></span>
                      <span className="text-stone-600">
                        {gapPercent}% of p
                        {isSweet && <span className="ml-1 text-emerald-700 font-semibold">Sweet spot!</span>}
                      </span>
                    </div>
                  </div>
                  {/* Show the calculation when it's interesting */}
                  {isExactlyBelow && (
                    <div className="text-[10px] text-amber-700 mt-1 bg-amber-100 rounded px-2 py-1">
                      <span className="font-mono">{prime} = {base}<sup>{blockSize}</sup> − {gap}</span>
                      <span className="text-amber-600 ml-2">→ prime is {gap} below {bPowK}</span>
                    </div>
                  )}
                </>
              );
            })()}
          </div>

          {/* Two gears explanation */}
          <div className="grid grid-cols-1 sm:grid-cols-2 gap-4 text-xs sm:text-sm">
            <div className="bg-amber-100/50 rounded p-3">
              <div className="font-semibold text-amber-800 mb-1">Fast Gear (×{base})</div>
              <div className="text-amber-700">
                One digit at a time. The fine dashed line.
              </div>
            </div>
            <div className="bg-rose-100/50 rounded p-3">
              <div className="font-semibold text-rose-800 mb-1">Slow Gear (×{blockMultiplier})</div>
              <div className="text-rose-700">
                Every {blockSize} digits. The bold red chords.
                <br />
                <span className="font-mono">ord<sub>{prime}</sub>({blockMultiplier}) = {blockOrder}</span>
              </div>
            </div>
          </div>

          <p className="text-amber-700 text-xs mt-3 leading-relaxed">
            Because {prime} is just {bPowK - prime} below {base}<sup>{blockSize}</sup>, moving {blockSize} digits
            forward multiplies the remainder by {blockMultiplier}. The "messy" digit snake is secretly
            threaded along a simple geometric orbit sampled every {blockSize} steps.
          </p>

          {/* Geometric Progression - The Core Insight */}
          <div className="mt-4 pt-3 border-t border-amber-200">
            <div className="font-semibold text-amber-800 mb-2 text-xs sm:text-sm">
              Block-Start Remainders: Geometric Progression
            </div>
            <div className="bg-amber-100/70 rounded-lg p-3 font-mono text-xs">
              <div className="flex flex-wrap items-center gap-1 mb-2">
                {blockStartRemainders.slice(0, 8).map((item, i) => (
                  <span key={i} className="flex items-center">
                    <span className={`px-2 py-1 rounded ${
                      item.isQR
                        ? 'bg-violet-200 text-violet-800 border border-violet-300'
                        : 'bg-rose-200 text-rose-800 border border-rose-300'
                    }`}>
                      {item.r}
                    </span>
                    {i < Math.min(blockStartRemainders.length - 1, 7) && (
                      <span className="text-amber-600 mx-1">→</span>
                    )}
                  </span>
                ))}
                {blockStartRemainders.length > 8 && <span className="text-stone-400">...</span>}
              </div>
              <div className="text-[10px] text-amber-700">
                {numerator} × {blockMultiplier}<sup>i</sup> (mod {prime}) for i = 0, 1, 2, ...
              </div>
            </div>

            {/* Coset Membership Insight */}
            <div className={`mt-3 p-3 rounded-lg text-xs ${
              orbitStaysInCoset ? 'bg-emerald-50 border border-emerald-200' : 'bg-orange-50 border border-orange-200'
            }`}>
              <div className="flex items-start gap-2">
                <span className="text-lg">{orbitStaysInCoset ? '🔒' : '🔄'}</span>
                <div>
                  <div className={`font-semibold mb-1 ${orbitStaysInCoset ? 'text-emerald-800' : 'text-orange-800'}`}>
                    {orbitStaysInCoset ? 'Coset Locked' : 'Coset Alternates'}
                  </div>
                  {orbitStaysInCoset ? (
                    <p className={numeratorIsQR ? 'text-violet-700' : 'text-rose-700'}>
                      <span className="font-semibold">d = {blockMultiplier}</span> is a QR, so multiplying preserves coset.
                      <br />
                      Your numerator {numerator} is {numeratorIsQR ? 'QR' : 'NQR'}, so the <em>entire orbit</em> stays
                      in the {numeratorIsQR ? 'QR (★)' : 'NQR (●)'} coset.
                    </p>
                  ) : (
                    <p className="text-orange-700">
                      <span className="font-semibold">d = {blockMultiplier}</span> is an NQR, so multiplying flips coset!
                      <br />
                      Block remainders alternate: {numeratorIsQR ? 'QR → NQR → QR → ...' : 'NQR → QR → NQR → ...'}
                    </p>
                  )}
                </div>
              </div>
            </div>
          </div>

          {/* Symmetry information */}
          <div className="mt-4 pt-3 border-t border-amber-200">
            <div className="font-semibold text-amber-800 mb-2 text-xs sm:text-sm">
              Symmetries
            </div>
            <div className="grid grid-cols-1 sm:grid-cols-2 gap-3 text-xs">
              {/* Polygon closure */}
              <div className="bg-rose-50 rounded p-2 border border-rose-200">
                <div className="font-semibold text-rose-800 mb-1">
                  Periodicity: {blockOrder}-gon
                </div>
                <div className="text-rose-700 font-mono text-[10px]">
                  {blockMultiplier}<sup>{blockOrder}</sup> ≡ 1 (mod {prime})
                </div>
                <div className="text-rose-600 text-[10px] mt-1">
                  The block orbit closes after {blockOrder} jumps, forming a {blockOrder}-sided polygon.
                </div>
              </div>

              {/* Antisymmetry */}
              <div className={`rounded p-2 border ${hasAntisymmetry ? 'bg-violet-50 border-violet-200' : 'bg-stone-50 border-stone-200'}`}>
                <div className={`font-semibold mb-1 ${hasAntisymmetry ? 'text-violet-800' : 'text-stone-500'}`}>
                  Antisymmetry: {hasAntisymmetry ? `at step ${antisymmetryIndex}` : 'none'}
                </div>
                {hasAntisymmetry ? (
                  <>
                    <div className="text-violet-700 font-mono text-[10px]">
                      {blockMultiplier}<sup>{antisymmetryIndex}</sup> ≡ −1 (mod {prime})
                    </div>
                    <div className="text-violet-600 text-[10px] mt-1">
                      After {antisymmetryIndex} block jumps, you land at the <em>opposite</em> point.
                      Blocks come in complementary pairs!
                    </div>
                  </>
                ) : (
                  <div className="text-stone-500 text-[10px]">
                    The multiplier {blockMultiplier} never reaches −1.
                    <br />
                    <span className="italic">(It's a quadratic residue mod {prime})</span>
                  </div>
                )}
              </div>
            </div>
          </div>
        </div>
      )}

      {/* Coset Comparison explainer */}
      {showCosetComparison && (
        <div className="mt-4 bg-fuchsia-50 border border-fuchsia-200 rounded-lg p-4 sm:p-5">
          <div className="font-semibold text-fuchsia-800 mb-2 text-sm sm:text-base">
            The Two Cosets
          </div>
          <p className="text-fuchsia-700 text-xs sm:text-sm leading-relaxed mb-3">
            The multiplicative group (ℤ/{prime}ℤ)* has {prime - 1} elements. The squaring map x → x² is 2-to-1,
            so exactly half are squares (QR) and half are non-squares (NQR).
          </p>
          <div className="grid grid-cols-2 gap-3 text-xs">
            <div className="bg-violet-100 rounded p-3 border border-violet-200">
              <div className="font-semibold text-violet-800 flex items-center gap-1">
                <span>★</span> QR Coset
              </div>
              <div className="text-violet-700 mt-1">
                {(prime - 1) / 2} quadratic residues
              </div>
              <div className="text-violet-600 text-[10px] mt-1">
                Numerator {numeratorIsQR ? numerator : contrastingNumerator}/{prime}
              </div>
            </div>
            <div className="bg-rose-100 rounded p-3 border border-rose-200">
              <div className="font-semibold text-rose-800 flex items-center gap-1">
                <span>●</span> NQR Coset
              </div>
              <div className="text-rose-700 mt-1">
                {(prime - 1) / 2} non-residues
              </div>
              <div className="text-rose-600 text-[10px] mt-1">
                Numerator {numeratorIsQR ? contrastingNumerator : numerator}/{prime}
              </div>
            </div>
          </div>
          <p className="text-fuchsia-600 text-xs mt-3">
            <strong>Key insight:</strong> The numerator selects the coset.
            Both orbits have identical structure — they're just different "halves" of the same group.
          </p>
        </div>
      )}

      {/* Shadow explainer - shown in default shadow view */}
      {!showBlockLayer && !showCosetComparison && (
        <div className="mt-4 bg-indigo-50 border border-indigo-200 rounded-lg p-4 sm:p-5">
          <div className="font-semibold text-indigo-800 mb-2 text-sm sm:text-base">
            The Decimal as Shadow
          </div>
          <p className="text-indigo-700 text-xs sm:text-sm leading-relaxed">
            The orbit on the circle is <strong>finite</strong> — it visits {period} points
            and returns to start. Each point casts a digit onto the number line below.
            When the orbit completes, the same shadow pattern repeats.
          </p>
          <p className="text-indigo-600 text-xs mt-2">
            The "infinite" repeating decimal is just this {period}-digit shadow on repeat.
          </p>

          {/* Coset insight - minimal */}
          <div className={`mt-2 pt-2 border-t border-indigo-200 text-xs flex items-center gap-2 ${
            numeratorIsQR ? 'text-violet-600' : 'text-rose-600'
          }`}>
            <span>{numeratorIsQR ? '★' : '●'}</span>
            <span>
              {numerator} is {numeratorIsQR ? 'QR' : 'NQR'} — orbit stays in the {numeratorIsQR ? 'QR' : 'NQR'} half
            </span>
          </div>
        </div>
      )}

    </div>
  );
};

export default CircleWalkPlayground;
