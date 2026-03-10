import { useState, useEffect, useRef, useCallback, useMemo } from 'react';

// =============================================================================
// Utilities
// =============================================================================

function modPow(base: number, exp: number, mod: number): number {
  let result = 1;
  base = base % mod;
  while (exp > 0) {
    if (exp % 2 === 1) result = (result * base) % mod;
    exp = Math.floor(exp / 2);
    base = (base * base) % mod;
  }
  return result;
}

function _multiplicativeOrder(base: number, mod: number): number {
  let current = base % mod;
  let order = 1;
  while (current !== 1 && order < mod) {
    current = (current * base) % mod;
    order++;
  }
  return order;
}
void _multiplicativeOrder; // available for future use

function isQuadraticResidue(x: number, prime: number): boolean {
  if (x % prime === 0) return false;
  const exp = (prime - 1) / 2;
  return modPow(x, exp, prime) === 1;
}

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

// =============================================================================
// Types
// =============================================================================

interface OrbitStep {
  t: number;          // step index
  remainder: number;  // current remainder (= state)
  digit: number;      // output digit
}

interface ThreeViewsUnificationProps {
  prime?: number;
  base?: number;
}

// =============================================================================
// Component
// =============================================================================

export default function ThreeViewsUnification({
  prime: initialPrime = 19,
  base: initialBase = 10,
}: ThreeViewsUnificationProps) {
  const [prime] = useState(initialPrime);
  const [base] = useState(initialBase);
  const [step, setStep] = useState(0);
  const [isPlaying, setIsPlaying] = useState(false);
  const [hasStarted, setHasStarted] = useState(false);
  const [activeView, setActiveView] = useState<'all' | 'circle' | 'fsm' | 'series'>('all');

  const containerRef = useRef<HTMLDivElement>(null);
  const intervalRef = useRef<ReturnType<typeof setInterval> | null>(null);
  const startTimeoutRef = useRef<ReturnType<typeof setTimeout> | null>(null);

  // Compute the orbit
  const orbit = useMemo((): OrbitStep[] => {
    const steps: OrbitStep[] = [];
    let r = 1;
    const seen = new Set<number>();

    while (!seen.has(r) && steps.length < prime) {
      seen.add(r);
      const product = r * base;
      const digit = Math.floor(product / prime);
      steps.push({ t: steps.length, remainder: r, digit });
      r = product % prime;
    }

    return steps;
  }, [prime, base]);

  const period = orbit.length;
  const k = base % prime; // bridge residue

  // Advance step
  const advanceStep = useCallback(() => {
    setStep((prev) => {
      if (prev >= period - 1) {
        setIsPlaying(false);
        return prev;
      }
      return prev + 1;
    });
  }, [period]);

  // IntersectionObserver for auto-play
  useEffect(() => {
    const startPlay = () => {
      if (!hasStarted) {
        setHasStarted(true);
        startTimeoutRef.current = setTimeout(() => {
          setIsPlaying(true);
        }, 600);
      }
    };

    if (typeof window === 'undefined' || typeof window.IntersectionObserver === 'undefined') {
      startPlay();
      return () => {
        if (startTimeoutRef.current) clearTimeout(startTimeoutRef.current);
      };
    }

    const observer = new window.IntersectionObserver(
      ([entry]) => {
        if (entry.isIntersecting && !hasStarted) {
          startPlay();
        }
      },
      { threshold: 0.4 }
    );

    if (containerRef.current) {
      observer.observe(containerRef.current);
    }

    return () => {
      observer.disconnect();
      if (startTimeoutRef.current) clearTimeout(startTimeoutRef.current);
    };
  }, [hasStarted]);

  // Animation interval
  useEffect(() => {
    if (isPlaying) {
      intervalRef.current = setInterval(advanceStep, 400);
    } else {
      if (intervalRef.current) {
        clearInterval(intervalRef.current);
        intervalRef.current = null;
      }
    }
    return () => {
      if (intervalRef.current) clearInterval(intervalRef.current);
    };
  }, [isPlaying, advanceStep]);

  // =============================================================================
  // Circle View
  // =============================================================================

  const CircleView = () => {
    const radius = 70;
    const cx = 90;
    const cy = 90;

    const getPos = (residue: number) => {
      const index = residue - 1;
      const total = prime - 1;
      const angle = (index / total) * 2 * Math.PI - Math.PI / 2;
      return {
        x: cx + Math.cos(angle) * radius,
        y: cy + Math.sin(angle) * radius,
      };
    };

    const visitedRemainders = orbit.slice(0, step + 1).map((s) => s.remainder);
    const currentRemainder = orbit[step]?.remainder;

    // Build path
    const pathPoints = visitedRemainders.map((r) => getPos(r));
    const pathD =
      pathPoints.length > 1
        ? `M ${pathPoints[0].x} ${pathPoints[0].y} ` +
          pathPoints.slice(1).map((pt) => `L ${pt.x} ${pt.y}`).join(' ')
        : '';

    return (
      <div className="flex flex-col items-center">
        <div className="text-[10px] font-mono text-stone-500 uppercase tracking-wide mb-2">
          Circle (Geometric)
        </div>
        <svg viewBox="0 0 180 180" className="w-40 h-40 sm:w-44 sm:h-44">
          {/* Outer circle */}
          <circle cx={cx} cy={cy} r={radius + 5} fill="none" stroke="#d6d3d1" strokeWidth="1" />

          {/* All residue points */}
          {Array.from({ length: prime - 1 }, (_, i) => i + 1).map((r) => {
            const pos = getPos(r);
            const isQR = isQuadraticResidue(r, prime);
            const isVisited = visitedRemainders.includes(r);
            const isCurrent = r === currentRemainder;

            const pointRadius = isCurrent ? 10 : isVisited ? 8 : 6;
            const fillColor = isCurrent
              ? '#10b981'
              : isVisited
              ? '#6ee7b7'
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
          <text x={cx} y={cy} textAnchor="middle" dominantBaseline="middle" className="text-[9px] font-mono fill-stone-400">
            (Z/{prime}Z)*
          </text>
        </svg>
        <div className="text-[10px] text-stone-600 text-center mt-1">
          r = <span className="font-mono font-bold text-emerald-700">{currentRemainder}</span>
        </div>
      </div>
    );
  };

  // =============================================================================
  // FSM View (Linear State Diagram)
  // =============================================================================

  const FSMView = () => {
    const visibleStates = Math.min(8, period);
    const boxW = 32;
    const boxH = 24;
    const gap = 12;
    const arrowLen = gap;
    const totalW = visibleStates * boxW + (visibleStates - 1) * (gap + arrowLen) + 40;

    return (
      <div className="flex flex-col items-center">
        <div className="text-[10px] font-mono text-stone-500 uppercase tracking-wide mb-2">
          State Machine (Computational)
        </div>
        <div className="overflow-x-auto max-w-full">
          <svg viewBox={`0 0 ${totalW} 80`} className="h-20 min-w-[280px]" style={{ width: totalW }}>
            {orbit.slice(0, visibleStates).map((s, i) => {
              const x = 20 + i * (boxW + gap + arrowLen);
              const y = 28;
              const isCurrent = i === step;
              const isVisited = i <= step;

              return (
                <g key={i}>
                  {/* State box */}
                  <rect
                    x={x}
                    y={y}
                    width={boxW}
                    height={boxH}
                    rx={4}
                    fill={isCurrent ? '#10b981' : isVisited ? '#d1fae5' : '#f5f5f4'}
                    stroke={isCurrent ? '#059669' : isVisited ? '#6ee7b7' : '#d6d3d1'}
                    strokeWidth={isCurrent ? 2 : 1}
                    className="transition-all duration-200"
                  />
                  {/* State label (remainder) */}
                  <text
                    x={x + boxW / 2}
                    y={y + boxH / 2 + 1}
                    textAnchor="middle"
                    dominantBaseline="middle"
                    className={`text-[10px] font-mono ${isCurrent ? 'fill-white font-bold' : 'fill-stone-700'}`}
                  >
                    {s.remainder}
                  </text>
                  {/* Output digit above */}
                  <text
                    x={x + boxW / 2}
                    y={y - 6}
                    textAnchor="middle"
                    className={`text-[9px] font-mono ${isVisited ? 'fill-amber-600' : 'fill-stone-400'}`}
                  >
                    d={s.digit}
                  </text>
                  {/* Transition arrow */}
                  {i < visibleStates - 1 && (
                    <>
                      <line
                        x1={x + boxW + 2}
                        y1={y + boxH / 2}
                        x2={x + boxW + gap + arrowLen - 6}
                        y2={y + boxH / 2}
                        stroke={i < step ? '#10b981' : '#d6d3d1'}
                        strokeWidth={1.5}
                        markerEnd="url(#arrowhead)"
                      />
                    </>
                  )}
                </g>
              );
            })}
            {/* Ellipsis if more states */}
            {period > visibleStates && (
              <text
                x={20 + visibleStates * (boxW + gap + arrowLen) - 10}
                y={40}
                className="text-[12px] fill-stone-400"
              >
                ...
              </text>
            )}
            {/* Arrow marker definition */}
            <defs>
              <marker id="arrowhead" markerWidth="6" markerHeight="6" refX="5" refY="3" orient="auto">
                <path d="M0,0 L6,3 L0,6 Z" fill="#a8a29e" />
              </marker>
            </defs>
          </svg>
        </div>
        <div className="text-[10px] text-stone-600 text-center mt-1">
          state = <span className="font-mono font-bold text-emerald-700">{orbit[step]?.remainder}</span>,
          output = <span className="font-mono font-bold text-amber-600">{orbit[step]?.digit}</span>
        </div>
      </div>
    );
  };

  // =============================================================================
  // Series View
  // =============================================================================

  const SeriesView = () => {
    const visibleTerms = Math.min(6, period);

    return (
      <div className="flex flex-col items-center">
        <div className="text-[10px] font-mono text-stone-500 uppercase tracking-wide mb-2">
          Series (Algebraic)
        </div>
        <div className="bg-stone-50 rounded-lg px-3 py-2 border border-stone-200">
          <div className="text-[10px] font-mono text-stone-600 mb-1">
            1/{prime} = <span className="text-stone-400">Σ</span> k<sup>j</sup> / {base}<sup>j+1</sup>
          </div>
          <div className="text-[10px] text-stone-500 mb-2">
            k = {base} mod {prime} = {k}
          </div>
          <div className="flex flex-wrap gap-1 items-center">
            {orbit.slice(0, visibleTerms).map((_, j) => {
              const isCurrent = j === step;
              const isVisited = j <= step;
              const kPowJ = modPow(k, j, prime);

              return (
                <span key={j} className="flex items-center">
                  <span
                    className={`px-1.5 py-0.5 rounded text-[10px] font-mono transition-all duration-200 ${
                      isCurrent
                        ? 'bg-emerald-500 text-white font-bold'
                        : isVisited
                        ? 'bg-emerald-100 text-emerald-800'
                        : 'bg-stone-100 text-stone-500'
                    }`}
                  >
                    {k}<sup>{j}</sup>={kPowJ}
                  </span>
                  {j < visibleTerms - 1 && <span className="text-stone-400 mx-0.5">+</span>}
                </span>
              );
            })}
            {period > visibleTerms && <span className="text-stone-400 text-[10px]">...</span>}
          </div>
        </div>
        <div className="text-[10px] text-stone-600 text-center mt-2">
          term j={step}: {k}<sup>{step}</sup> ≡{' '}
          <span className="font-mono font-bold text-emerald-700">{modPow(k, step, prime)}</span> (mod {prime})
        </div>
      </div>
    );
  };

  // =============================================================================
  // Controls
  // =============================================================================

  const handlePlayPause = () => {
    if (step >= period - 1) {
      setStep(0);
      setTimeout(() => setIsPlaying(true), 100);
    } else {
      setIsPlaying((prev) => !prev);
    }
  };

  const handlePrev = () => {
    setIsPlaying(false);
    setStep((prev) => Math.max(0, prev - 1));
  };

  const handleNext = () => {
    setIsPlaying(false);
    setStep((prev) => Math.min(period - 1, prev + 1));
  };

  const handleReset = () => {
    setIsPlaying(false);
    setStep(0);
  };

  // =============================================================================
  // Render
  // =============================================================================

  const showAll = activeView === 'all';

  return (
    <div
      ref={containerRef}
      className="bg-white border border-stone-200 rounded-xl shadow-lg overflow-hidden"
    >
      {/* Header */}
      <div className="bg-gradient-to-r from-indigo-800 to-violet-700 px-4 sm:px-5 py-3">
        <span className="text-[10px] sm:text-xs font-mono text-indigo-300 uppercase tracking-wider">
          Interactive
        </span>
        <h3 className="text-white font-semibold text-sm">
          Three Views, One Object
        </h3>
      </div>

      {/* View selector (mobile) */}
      <div className="sm:hidden flex border-b border-stone-200">
        {(['all', 'circle', 'fsm', 'series'] as const).map((v) => (
          <button
            key={v}
            onClick={() => setActiveView(v)}
            className={`flex-1 py-2 text-xs font-mono transition-colors ${
              activeView === v
                ? 'bg-indigo-100 text-indigo-800 font-semibold'
                : 'text-stone-600 hover:bg-stone-50'
            }`}
          >
            {v === 'all' ? 'All' : v === 'circle' ? 'Circle' : v === 'fsm' ? 'Machine' : 'Series'}
          </button>
        ))}
      </div>

      {/* Main content */}
      <div className="p-4 sm:p-5">
        {/* Triptych */}
        <div className={`grid gap-4 ${showAll ? 'sm:grid-cols-3' : 'grid-cols-1'}`}>
          {(showAll || activeView === 'circle') && <CircleView />}
          {(showAll || activeView === 'fsm') && <FSMView />}
          {(showAll || activeView === 'series') && <SeriesView />}
        </div>

        {/* Correspondence callout */}
        <div className="mt-4 bg-indigo-50 border border-indigo-200 rounded-lg p-3">
          <div className="text-xs text-indigo-800">
            <span className="font-semibold">Isomorphism:</span>{' '}
            Circle node <span className="font-mono bg-indigo-100 px-1 rounded">{orbit[step]?.remainder}</span>{' '}
            = state machine state{' '}
            = remainder after {step} multiplications by {base}{' '}
            = coefficient {k}<sup>{step}</sup> mod {prime}
          </div>
          <div className="text-[10px] text-indigo-600 mt-1">
            (Computer scientists call this a finite-state machine, or FSM—also known as a DFA.)
          </div>
        </div>

        {/* Controls */}
        <div className="flex justify-center items-center gap-2 mt-4 flex-wrap">
          <button
            onClick={handleReset}
            className="px-3 py-1.5 text-xs font-mono bg-stone-100 border border-stone-300 rounded hover:bg-stone-200 transition-colors"
          >
            ↺ Reset
          </button>
          <button
            onClick={handlePrev}
            disabled={step === 0}
            className="px-3 py-1.5 text-xs font-mono bg-stone-100 border border-stone-300 rounded hover:bg-stone-200 disabled:opacity-30 transition-colors"
          >
            ← Prev
          </button>
          <button
            onClick={handlePlayPause}
            className={`px-4 py-1.5 text-xs font-mono rounded transition-colors min-w-[80px] ${
              isPlaying
                ? 'bg-stone-600 text-white hover:bg-stone-700'
                : step >= period - 1
                ? 'bg-amber-500 text-white hover:bg-amber-600'
                : 'bg-indigo-600 text-white hover:bg-indigo-700'
            }`}
          >
            {isPlaying ? '⏸ Pause' : step >= period - 1 ? '↺ Replay' : '▶ Play'}
          </button>
          <button
            onClick={handleNext}
            disabled={step >= period - 1}
            className="px-3 py-1.5 text-xs font-mono bg-stone-100 border border-stone-300 rounded hover:bg-stone-200 disabled:opacity-30 transition-colors"
          >
            Next →
          </button>

          {/* Progress indicator */}
          <div className="ml-2 text-xs font-mono text-stone-500">
            {step + 1}/{period}
          </div>
        </div>
      </div>

      {/* Footer insight */}
      <div className="bg-gradient-to-r from-indigo-50 to-violet-50 border-t border-indigo-100 px-4 sm:px-5 py-3">
        <p className="text-xs text-indigo-900 mb-2">
          <strong>The punchline:</strong> Long division is a finite-state machine—a
          system with only {period} possible states (the remainders). Each remainder
          determines the next digit and the next state. Since there are only finitely
          many remainders, you <em>must</em> eventually revisit one—and from that point,
          the entire future is determined.
        </p>
        <p className="text-[10px] text-indigo-700">
          This is Lagrange's theorem in action: the orbit length must divide the group
          order. For prime p, that's p−1. The "infinite" decimal is inevitable finiteness
          in disguise.
        </p>
      </div>
    </div>
  );
}
