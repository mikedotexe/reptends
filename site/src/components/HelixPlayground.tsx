import { useState, useEffect, useRef, useCallback, useMemo } from 'react';
import OrbitHelix3D from './OrbitHelix3D';
import { multiplicativeOrder } from '../lib/math';

/**
 * Interactive playground for the 3D helix visualization.
 * Shows the dual helix with controls for prime, base, and animation.
 */
const HelixPlayground = () => {
  const [prime, setPrime] = useState(19);
  const [base, setBase] = useState(10);
  const [step, setStep] = useState(0);
  const [isPlaying, setIsPlaying] = useState(false);
  const [showBothHelixes, setShowBothHelixes] = useState(true);
  const intervalRef = useRef<ReturnType<typeof setInterval> | null>(null);

  const k = base % prime;
  const orbitLength = multiplicativeOrder(k, prime);

  // Compute weave and flux for display
  const computeWF = useCallback(() => {
    if (orbitLength === 0) return { W: 0, F: 0, R: 0 };
    // Use BigInt for large numbers
    const kL = BigInt(k) ** BigInt(orbitLength);
    const BL = BigInt(base) ** BigInt(orbitLength);
    const p = BigInt(prime);

    const R = (BL - 1n) / p;
    const W = (BL - kL) / p;
    const F = (kL - 1n) / p;

    return {
      R: Number(R),
      W: Number(W),
      F: Number(F),
    };
  }, [k, base, prime, orbitLength]);

  const { W, F } = computeWF();

  // Cone angle θ = arctan(log(k)/log(B)) encodes growth rate ratio
  // When k ≈ B: θ → 45° (similar growth rates)
  // When k << B: θ → 0° (k grows much slower, steep narrow cone)
  const coneAngle = useMemo(() => {
    if (k <= 1 || base <= 1) return 45; // default for edge cases
    const ratio = Math.log(k) / Math.log(base);
    const angleRad = Math.atan(ratio);
    const angleDeg = (angleRad * 180) / Math.PI;
    return Math.round(angleDeg * 10) / 10; // Round to 1 decimal
  }, [k, base]);

  const advanceStep = useCallback(() => {
    setStep((prev) => {
      if (prev >= orbitLength) {
        setIsPlaying(false);
        return prev;
      }
      return prev + 1;
    });
  }, [orbitLength]);

  useEffect(() => {
    if (isPlaying) {
      intervalRef.current = setInterval(advanceStep, 600);
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

  useEffect(() => {
    if (step >= orbitLength) setIsPlaying(false);
  }, [step, orbitLength]);

  // Reset step when prime/base changes
  useEffect(() => {
    setStep(0);
    setIsPlaying(false);
  }, [prime, base]);

  const handlePlayPause = () => {
    if (step >= orbitLength) {
      setStep(0);
      setTimeout(() => setIsPlaying(true), 100);
    } else {
      setIsPlaying((prev) => !prev);
    }
  };

  const primeOptions = [7, 13, 17, 19, 23, 31, 37, 41, 43, 47, 97];
  const baseOptions = [2, 3, 5, 7, 10, 12];

  return (
    <div className="my-8 bg-white border border-stone-200 rounded-xl shadow-lg overflow-hidden">
      {/* Header */}
      <div className="bg-gradient-to-r from-indigo-900 to-violet-900 px-4 py-3">
        <span className="text-[10px] font-mono text-indigo-300 uppercase tracking-wider">
          Interactive 3D
        </span>
        <h3 className="text-stone-100 font-semibold text-sm">
          The Double Helix: Two Runners, One Track
        </h3>
      </div>

      {/* Main content */}
      <div className="p-4">
        {/* Controls row */}
        <div className="flex flex-wrap gap-4 mb-4 items-center">
          <div className="flex items-center gap-2">
            <label className="text-xs font-mono text-stone-500">Prime:</label>
            <select
              value={prime}
              onChange={(e) => setPrime(Number(e.target.value))}
              className="text-xs font-mono border border-stone-300 rounded px-2 py-1"
            >
              {primeOptions.map((p) => (
                <option key={p} value={p}>
                  {p}
                </option>
              ))}
            </select>
          </div>

          <div className="flex items-center gap-2">
            <label className="text-xs font-mono text-stone-500">Base:</label>
            <select
              value={base}
              onChange={(e) => setBase(Number(e.target.value))}
              className="text-xs font-mono border border-stone-300 rounded px-2 py-1"
            >
              {baseOptions.map((b) => (
                <option key={b} value={b}>
                  {b}
                </option>
              ))}
            </select>
          </div>

          <label className="flex items-center gap-2 text-xs font-mono text-stone-500">
            <input
              type="checkbox"
              checked={showBothHelixes}
              onChange={(e) => setShowBothHelixes(e.target.checked)}
              className="rounded"
            />
            Show both helixes
          </label>
        </div>

        {/* 3D visualization */}
        <div className="relative">
          <OrbitHelix3D
            prime={prime}
            base={base}
            currentStep={step}
            showBothHelixes={showBothHelixes}
          />
        </div>

        {/* Stats panel */}
        <div className="mt-4 grid grid-cols-2 sm:grid-cols-5 gap-2 text-xs font-mono">
          <div className="bg-emerald-50 border border-emerald-200 rounded p-2">
            <div className="text-emerald-600 text-[10px] uppercase">k (skeleton)</div>
            <div className="text-emerald-800 font-bold">{k}</div>
          </div>
          <div className="bg-indigo-50 border border-indigo-200 rounded p-2">
            <div className="text-indigo-600 text-[10px] uppercase">Orbit length</div>
            <div className="text-indigo-800 font-bold">{orbitLength}</div>
          </div>
          <div className="bg-violet-50 border border-violet-200 rounded p-2">
            <div className="text-violet-600 text-[10px] uppercase">Cone θ</div>
            <div className="text-violet-800 font-bold">{coneAngle}°</div>
          </div>
          <div className="bg-stone-50 border border-stone-200 rounded p-2">
            <div className="text-stone-500 text-[10px] uppercase">Weave W</div>
            <div className="text-stone-800 font-bold">{W.toLocaleString()}</div>
          </div>
          <div className="bg-amber-50 border border-amber-200 rounded p-2">
            <div className="text-amber-600 text-[10px] uppercase">Flux F</div>
            <div className="text-amber-800 font-bold">{F.toLocaleString()}</div>
          </div>
        </div>

        {/* Animation controls */}
        <div className="mt-4 flex justify-center items-center gap-2">
          <button
            onClick={() => {
              setStep(0);
              setIsPlaying(false);
            }}
            className="px-3 py-1.5 text-xs font-mono bg-stone-100 border border-stone-300 rounded hover:bg-stone-200 transition-colors"
          >
            ↺ Reset
          </button>
          <button
            onClick={() => setStep((s) => Math.max(0, s - 1))}
            disabled={step === 0}
            className="px-3 py-1.5 text-xs font-mono bg-stone-100 border border-stone-300 rounded hover:bg-stone-200 disabled:opacity-30 transition-colors"
          >
            ← Prev
          </button>
          <button
            onClick={handlePlayPause}
            className={`px-4 py-1.5 text-xs font-mono rounded min-w-[80px] transition-colors ${
              isPlaying
                ? 'bg-stone-600 text-white'
                : step >= orbitLength
                ? 'bg-amber-500 text-white'
                : 'bg-indigo-600 text-white hover:bg-indigo-700'
            }`}
          >
            {isPlaying ? '⏸ Pause' : step >= orbitLength ? '↺ Replay' : '▶ Play'}
          </button>
          <button
            onClick={() => setStep((s) => Math.min(orbitLength, s + 1))}
            disabled={step >= orbitLength}
            className="px-3 py-1.5 text-xs font-mono bg-stone-100 border border-stone-300 rounded hover:bg-stone-200 disabled:opacity-30 transition-colors"
          >
            Next →
          </button>

          {/* Progress indicator */}
          <div className="ml-4 flex items-center gap-1">
            {Array.from({ length: orbitLength + 1 }, (_, i) => (
              <div
                key={i}
                className={`w-1.5 h-1.5 rounded-full transition-all ${
                  i < step
                    ? 'bg-indigo-500'
                    : i === step
                    ? 'bg-indigo-400 scale-125'
                    : 'bg-stone-200'
                }`}
              />
            ))}
          </div>
        </div>
      </div>

      {/* Explanation footer */}
      <div className="bg-gradient-to-r from-indigo-50 to-violet-50 border-t border-indigo-100 px-4 py-3">
        <p className="text-xs text-indigo-900">
          <strong>Two runners, one cone:</strong> The{' '}
          <span className="text-emerald-600">green helix (k={k})</span> and{' '}
          <span className="text-indigo-600">blue helix (B={base})</span> climb the cone,
          visiting the same positions mod {prime} at its base. At closure, the{' '}
          <span className="text-amber-600">amber mirror cone</span> appears below—the flux,
          a shadow world where the correction needed to close the orbit lives.
        </p>
      </div>
    </div>
  );
};

export default HelixPlayground;
