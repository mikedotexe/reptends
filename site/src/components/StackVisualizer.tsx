import { useState, useMemo, useEffect, useRef, useCallback } from 'react';
import OrbitClock from './OrbitClock';

interface TermData {
  power: number;
  exp: number;
  val: bigint;
  position: number;
}

/**
 * Interactive visualization showing how powers of 5 stack into the reptend.
 * Features auto-play on scroll, play/pause controls, and step-through animation.
 */
const StackVisualizer = () => {
  const [step, setStep] = useState(0);
  const [isPlaying, setIsPlaying] = useState(false);
  const [hasStarted, setHasStarted] = useState(false);
  const intervalRef = useRef<ReturnType<typeof setInterval> | null>(null);
  const containerRef = useRef<HTMLDivElement>(null);
  const startTimeoutRef = useRef<ReturnType<typeof setTimeout> | null>(null);

  const terms = useMemo<TermData[]>(() => {
    const powers = [5, 25, 125, 625, 3125, 15625, 78125, 390625, 1953125];
    return powers.map((p, i) => {
      const exp = 16 - 2 * i;
      const val = BigInt(p) * 10n ** BigInt(exp);
      return { power: p, exp, val, position: i };
    });
  }, []);

  const R = 52631578947368421n;
  const F = 102796n;
  const maxStep = 10;

  const runningSum = useMemo(() => {
    if (step === 0) return 0n;
    return terms
      .slice(0, Math.min(step, 9))
      .reduce((acc, t) => acc + t.val, 0n);
  }, [step, terms]);

  const showFlux = step >= 10;

  const advanceStep = useCallback(() => {
    setStep((prev) => {
      if (prev >= maxStep) {
        setIsPlaying(false);
        return prev;
      }
      return prev + 1;
    });
  }, []);

  // SSR-safe IntersectionObserver for auto-play
  useEffect(() => {
    const startPlay = () => {
      if (!hasStarted) {
        setHasStarted(true);
        startTimeoutRef.current = setTimeout(() => {
          setIsPlaying(true);
        }, 800);
      }
    };

    if (
      typeof window === 'undefined' ||
      typeof window.IntersectionObserver === 'undefined'
    ) {
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
      { threshold: 0.5 }
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
      intervalRef.current = setInterval(advanceStep, 900);
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

  // Stop when reaching end
  useEffect(() => {
    if (step >= maxStep) setIsPlaying(false);
  }, [step]);

  const handlePlayPause = () => {
    if (step >= maxStep) {
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
    setStep((prev) => Math.min(maxStep, prev + 1));
  };

  const handleReset = () => {
    setIsPlaying(false);
    setStep(0);
  };

  const formatDigits = (num: bigint, highlight = false, color = 'stone') => {
    const str = num.toString().padStart(18, '0');
    return str.split('').map((d, i) => (
      <span
        key={i}
        className={`inline-block w-2.5 sm:w-3 text-center transition-all duration-200 ${
          d === '0'
            ? 'text-stone-300'
            : highlight
            ? color === 'amber'
              ? 'text-amber-600 font-bold'
              : 'text-emerald-600 font-bold'
            : 'text-stone-700'
        }`}
      >
        {d === '0' ? '·' : d}
      </span>
    ));
  };

  const orbit = [5, 6, 11, 17, 9, 7, 16, 4, 1];

  return (
    <div
      ref={containerRef}
      className="my-8 sm:my-10 bg-white border border-stone-200 rounded-xl shadow-lg overflow-hidden"
    >
      {/* Header */}
      <div className="bg-gradient-to-r from-stone-800 to-stone-700 px-4 sm:px-5 py-3 flex flex-col sm:flex-row sm:justify-between sm:items-center gap-2">
        <div>
          <span className="text-[10px] sm:text-xs font-mono text-stone-400 uppercase tracking-wider">
            Interactive
          </span>
          <h3 className="text-stone-100 font-semibold text-sm">
            Building the Stack: Nine Powers of 5
          </h3>
        </div>
        <span
          className={`text-xs font-mono px-2 py-1 rounded self-start sm:self-auto ${
            step === 0
              ? 'bg-stone-600 text-stone-300'
              : step < 10
              ? 'bg-emerald-600 text-white'
              : 'bg-amber-500 text-white'
          }`}
        >
          {step === 0 ? 'Ready' : step < 10 ? `Term ${step}/9` : 'Complete'}
        </span>
      </div>

      {/* Main content */}
      <div className="p-4 sm:p-5">
        <div className="flex flex-col lg:flex-row gap-4 lg:gap-6">
          {/* Orbit clock */}
          <div className="lg:w-56 flex-shrink-0">
            <div className="text-[10px] sm:text-xs font-mono text-stone-500 uppercase tracking-wide mb-2 text-center">
              The Orbit (mod 19)
            </div>
            <OrbitClock currentStep={step} orbit={orbit} />
            <div className="text-[10px] sm:text-xs text-stone-500 text-center mt-2 leading-relaxed">
              5 generates the 9<br />quadratic residues
            </div>
          </div>

          {/* Digit grid */}
          <div className="flex-1 min-w-0">
            <div className="text-[10px] sm:text-xs font-mono text-stone-500 uppercase tracking-wide mb-2">
              The Positional Window (18 digits)
            </div>

            <div className="font-mono text-[10px] sm:text-xs space-y-0.5 mb-4 overflow-x-auto">
              {/* Position header */}
              <div className="flex items-center text-stone-400 mb-2 min-w-max">
                <span className="w-20 sm:w-28 text-right pr-2 sm:pr-3 text-stone-500 text-[9px] sm:text-[10px] hidden sm:block">
                  position →
                </span>
                <div className="flex">
                  {Array.from({ length: 18 }, (_, i) => (
                    <span key={i} className="w-2.5 sm:w-3 text-center text-[8px] sm:text-[9px]">
                      {17 - i}
                    </span>
                  ))}
                </div>
              </div>

              {/* Term rows */}
              {terms.map((term, i) => {
                const isActive = i < step;
                const isCurrent = i === step - 1 && step <= 9;
                const valStr = term.val.toString().padStart(18, '0');
                return (
                  <div
                    key={i}
                    className={`flex items-center transition-all duration-300 min-w-max ${
                      isActive ? 'opacity-100' : 'opacity-20'
                    } ${isCurrent ? 'bg-emerald-50 -mx-2 px-2 rounded' : ''}`}
                  >
                    <span className="w-20 sm:w-28 text-right pr-2 sm:pr-3 text-stone-500 text-[10px] sm:text-[11px]">
                      5<sup className="text-[8px] sm:text-[9px]">{i + 1}</sup> × 10
                      <sup className="text-[8px] sm:text-[9px]">{term.exp}</sup>
                    </span>
                    <div className="flex">
                      {valStr.split('').map((d, j) => (
                        <span
                          key={j}
                          className={`w-2.5 sm:w-3 text-center transition-all duration-200 ${
                            d === '0'
                              ? 'text-stone-300'
                              : isCurrent
                              ? 'text-emerald-600 font-bold'
                              : isActive
                              ? 'text-stone-600'
                              : 'text-stone-400'
                          }`}
                        >
                          {d === '0' ? '·' : d}
                        </span>
                      ))}
                    </div>
                  </div>
                );
              })}

              {/* Divider */}
              <div className="flex items-center my-3 min-w-max">
                <span className="w-20 sm:w-28"></span>
                <div className="flex-1 border-t border-dashed border-stone-300"></div>
              </div>

              {/* Running sum S */}
              <div
                className={`flex items-center min-w-max transition-all duration-300 ${
                  step > 0 ? 'opacity-100' : 'opacity-30'
                }`}
              >
                <span className="w-20 sm:w-28 text-right pr-2 sm:pr-3 text-stone-700 font-semibold text-[10px] sm:text-[11px]">
                  S =
                </span>
                <div className="flex">{formatDigits(runningSum, step > 0 && step <= 9)}</div>
              </div>

              {/* Flux row */}
              <div
                className={`flex items-center min-w-max transition-all duration-500 ${
                  showFlux ? 'opacity-100' : 'opacity-0 h-0 overflow-hidden'
                }`}
              >
                <span className="w-20 sm:w-28 text-right pr-2 sm:pr-3 text-amber-600 font-semibold text-[10px] sm:text-[11px]">
                  + F =
                </span>
                <div className="flex">{formatDigits(F, true, 'amber')}</div>
              </div>

              {/* Final divider */}
              {showFlux && (
                <div className="flex items-center my-2 min-w-max">
                  <span className="w-20 sm:w-28"></span>
                  <div className="flex-1 border-t-2 border-stone-400"></div>
                </div>
              )}

              {/* Result R */}
              <div
                className={`flex items-center min-w-max transition-all duration-500 ${
                  showFlux
                    ? 'opacity-100 bg-stone-100 -mx-2 px-2 py-1 rounded'
                    : 'opacity-30'
                }`}
              >
                <span className="w-20 sm:w-28 text-right pr-2 sm:pr-3 text-stone-900 font-bold text-[10px] sm:text-[11px]">
                  R =
                </span>
                <div className="flex">
                  {formatDigits(showFlux ? R : runningSum, showFlux)}
                </div>
              </div>
            </div>
          </div>
        </div>

        {/* Status message */}
        <div className="text-xs sm:text-sm text-stone-600 text-center my-4 h-10 flex items-center justify-center">
          {step === 0 && (
            <span className="text-stone-500">
              Watch the orbit unfold and terms stack into the window...
            </span>
          )}
          {step > 0 && step <= 9 && (
            <span>
              <span className="text-emerald-700 font-medium">Step {step}:</span>{' '}
              5<sup>{step}</sup> ≡ <strong>{orbit[step - 1]}</strong> (mod 19),
              placed at 10<sup>{terms[step - 1].exp}</sup>
            </span>
          )}
          {step === 10 && (
            <span className="text-amber-700 font-medium">
              Flux F = 102,796 completes the reptend. The orbit is now fully
              "dressed" in decimal.
            </span>
          )}
        </div>

        {/* Controls */}
        <div className="flex justify-center items-center gap-2 flex-wrap">
          <button
            onClick={handleReset}
            className="px-3 py-1.5 min-h-[36px] text-xs font-mono bg-stone-100 border border-stone-300 rounded hover:bg-stone-200 transition-colors"
          >
            ↺ Reset
          </button>
          <button
            onClick={handlePrev}
            disabled={step === 0}
            className="px-3 py-1.5 min-h-[36px] text-xs font-mono bg-stone-100 border border-stone-300 rounded hover:bg-stone-200 disabled:opacity-30 disabled:cursor-not-allowed transition-colors"
          >
            ← Prev
          </button>
          <button
            onClick={handlePlayPause}
            className={`px-4 py-1.5 min-h-[36px] text-xs font-mono rounded transition-colors min-w-[80px] ${
              isPlaying
                ? 'bg-stone-600 text-white hover:bg-stone-700'
                : step >= maxStep
                ? 'bg-amber-500 text-white hover:bg-amber-600'
                : 'bg-emerald-600 text-white hover:bg-emerald-700'
            }`}
          >
            {isPlaying ? '⏸ Pause' : step >= maxStep ? '↺ Replay' : '▶ Play'}
          </button>
          <button
            onClick={handleNext}
            disabled={step >= maxStep}
            className="px-3 py-1.5 min-h-[36px] text-xs font-mono bg-stone-100 border border-stone-300 rounded hover:bg-stone-200 disabled:opacity-30 disabled:cursor-not-allowed transition-colors"
          >
            Next →
          </button>

          {/* Progress dots */}
          <div className="ml-2 sm:ml-4 flex items-center gap-1">
            {Array.from({ length: 11 }, (_, i) => (
              <div
                key={i}
                className={`w-1.5 h-1.5 sm:w-2 sm:h-2 rounded-full transition-all duration-200 ${
                  i < step
                    ? i < 9
                      ? 'bg-emerald-500'
                      : 'bg-amber-500'
                    : i === step
                    ? 'bg-stone-400 scale-125'
                    : 'bg-stone-200'
                }`}
              />
            ))}
          </div>
        </div>
      </div>

      {/* Completion insight */}
      {showFlux && (
        <div className="bg-gradient-to-r from-amber-50 to-amber-100 border-t border-amber-200 px-4 sm:px-5 py-3 sm:py-4">
          <p className="text-xs sm:text-sm text-amber-900">
            <strong>Key insight:</strong> The orbit on the left shows 5 visiting
            all 9 quadratic residues. The staircase on the right shows those
            same powers <em>positioned</em> in the decimal window. The flux is
            the finite adjustment between the multiplicative orbit and its
            positional shadow.
          </p>
        </div>
      )}
    </div>
  );
};

export default StackVisualizer;
