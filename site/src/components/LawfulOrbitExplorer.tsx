import { useEffect, useEffectEvent, useMemo, useState } from 'react';

type OrbitKind = 'pure-periodic' | 'preperiodic' | 'terminating';

interface OrbitExample {
  key: string;
  label: string;
  denominator: number;
  numerator: number;
  base: number;
  theme: string;
  summary: string;
}

interface Step {
  index: number;
  remainder: number;
  digit: number;
  nextRemainder: number;
}

interface TraceSummary {
  kind: OrbitKind;
  steps: Step[];
  uniqueRemainders: number[];
  preperiod: number;
  period: number;
  strippedCore: number;
  basePrimeFactors: number[];
}

interface Point {
  x: number;
  y: number;
}

const DIGIT_CHARS = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ';

const orbitExamples: OrbitExample[] = [
  {
    key: 'one-seventh',
    label: '1/7',
    denominator: 7,
    numerator: 1,
    base: 10,
    theme: 'Pure loop',
    summary:
      'No base factors interfere, so the walk stays inside nonzero remainders and closes into a six-state cycle.',
  },
  {
    key: 'one-sixth',
    label: '1/6',
    denominator: 6,
    numerator: 1,
    base: 10,
    theme: 'Preperiod then loop',
    summary:
      'A base factor creates a short runway, then the dynamics settles into a repeating core instead of reaching 0.',
  },
  {
    key: 'one-eighth',
    label: '1/8',
    denominator: 8,
    numerator: 1,
    base: 10,
    theme: 'Termination',
    summary:
      'Because the denominator is built from base factors, the machine can fall into remainder 0 and the digits stop.',
  },
];

function formatDigit(digit: number): string {
  return DIGIT_CHARS[digit] ?? '?';
}

function uniquePrimeFactors(n: number): number[] {
  const factors: number[] = [];
  let value = Math.abs(Math.trunc(n));

  if (value < 2) {
    return factors;
  }

  if (value % 2 === 0) {
    factors.push(2);
    while (value % 2 === 0) {
      value = Math.trunc(value / 2);
    }
  }

  for (let p = 3; p * p <= value; p += 2) {
    if (value % p === 0) {
      factors.push(p);
      while (value % p === 0) {
        value = Math.trunc(value / p);
      }
    }
  }

  if (value > 1) {
    factors.push(value);
  }

  return factors;
}

function stripBaseFactors(n: number, base: number): { strippedCore: number; basePrimeFactors: number[] } {
  const basePrimeFactors = uniquePrimeFactors(base);
  let strippedCore = Math.abs(Math.trunc(n));

  for (const prime of basePrimeFactors) {
    while (strippedCore > 1 && strippedCore % prime === 0) {
      strippedCore = Math.trunc(strippedCore / prime);
    }
  }

  return { strippedCore, basePrimeFactors };
}

function buildTrace(example: OrbitExample): TraceSummary {
  const steps: Step[] = [];
  const seen = new Map<number, number>();
  let remainder = ((example.numerator % example.denominator) + example.denominator) % example.denominator;
  const { strippedCore, basePrimeFactors } = stripBaseFactors(example.denominator, example.base);

  let kind: OrbitKind = 'pure-periodic';
  let preperiod = 0;
  let period = 0;

  for (let index = 0; index < example.denominator + 4; index++) {
    if (remainder === 0) {
      kind = 'terminating';
      preperiod = steps.length;
      period = 0;
      break;
    }

    const seenAt = seen.get(remainder);
    if (seenAt != null) {
      preperiod = seenAt;
      period = steps.length - seenAt;
      kind = seenAt === 0 ? 'pure-periodic' : 'preperiodic';
      break;
    }

    seen.set(remainder, steps.length);
    const scaled = example.base * remainder;
    const digit = Math.floor(scaled / example.denominator);
    const nextRemainder = scaled % example.denominator;
    steps.push({ index, remainder, digit, nextRemainder });
    remainder = nextRemainder;
  }

  return {
    kind,
    steps,
    uniqueRemainders: Array.from(seen.keys()),
    preperiod,
    period,
    strippedCore,
    basePrimeFactors,
  };
}

function nodePositions(states: number[], includeZeroSink: boolean): Map<number, Point> {
  const centerY = includeZeroSink ? 88 : 100;
  const radius = includeZeroSink ? 62 : 68;
  const points = new Map<number, Point>();

  if (states.length === 1) {
    points.set(states[0], { x: 100, y: centerY - radius });
  } else {
    states.forEach((state, index) => {
      const angle = -Math.PI / 2 + (2 * Math.PI * index) / states.length;
      points.set(state, {
        x: 100 + Math.cos(angle) * radius,
        y: centerY + Math.sin(angle) * radius,
      });
    });
  }

  if (includeZeroSink) {
    points.set(0, { x: 100, y: 182 });
  }

  return points;
}

function offsetPoint(from: Point, to: Point, distance: number): Point {
  const dx = to.x - from.x;
  const dy = to.y - from.y;
  const length = Math.hypot(dx, dy) || 1;

  return {
    x: from.x + (dx / length) * distance,
    y: from.y + (dy / length) * distance,
  };
}

function edgePath(from: number, to: number, points: Map<number, Point>, radius: number): string {
  const start = points.get(from);
  const end = points.get(to);

  if (!start || !end) {
    return '';
  }

  if (from === to) {
    return [
      `M ${start.x - radius * 0.75} ${start.y - radius * 0.15}`,
      `C ${start.x - radius * 1.45} ${start.y - radius * 1.25},`,
      `${start.x + radius * 1.45} ${start.y - radius * 1.25},`,
      `${start.x + radius * 0.75} ${start.y - radius * 0.15}`,
    ].join(' ');
  }

  const pathStart = offsetPoint(start, end, radius);
  const pathEnd = offsetPoint(end, start, radius);

  return `M ${pathStart.x} ${pathStart.y} L ${pathEnd.x} ${pathEnd.y}`;
}

const kindPillStyles: Record<OrbitKind, string> = {
  'pure-periodic': 'bg-emerald-100 text-emerald-900',
  preperiodic: 'bg-amber-100 text-amber-900',
  terminating: 'bg-rose-100 text-rose-900',
};

const LawfulOrbitExplorer = () => {
  const [exampleKey, setExampleKey] = useState(orbitExamples[0].key);
  const [step, setStep] = useState(0);
  const [isPlaying, setIsPlaying] = useState(false);
  const [speedMs, setSpeedMs] = useState(900);

  const example = orbitExamples.find((entry) => entry.key === exampleKey) ?? orbitExamples[0];
  const trace = useMemo(() => buildTrace(example), [example]);
  const positions = useMemo(
    () => nodePositions(trace.uniqueRemainders, trace.kind === 'terminating'),
    [trace.kind, trace.uniqueRemainders],
  );
  const maxStep = trace.steps.length;
  const currentRemainder =
    step === 0
      ? trace.steps[0]?.remainder ?? 0
      : trace.steps[Math.min(step, trace.steps.length) - 1]?.nextRemainder ?? 0;
  const currentTransition = step < trace.steps.length ? trace.steps[step] : null;
  const emittedDigits = trace.steps.slice(0, step).map((entry) => entry.digit);
  const nodeRadius = 14;

  const advance = useEffectEvent(() => {
    setStep((current) => {
      if (current >= maxStep) {
        setIsPlaying(false);
        return current;
      }

      return current + 1;
    });
  });

  useEffect(() => {
    if (!isPlaying) {
      return;
    }

    const timer = window.setInterval(() => {
      advance();
    }, speedMs);

    return () => window.clearInterval(timer);
  }, [advance, isPlaying, speedMs]);

  useEffect(() => {
    setStep(0);
    setIsPlaying(false);
  }, [exampleKey]);

  const summaryLabel =
    trace.kind === 'pure-periodic'
      ? `Loop length ${trace.period}`
      : trace.kind === 'preperiodic'
      ? `Preperiod ${trace.preperiod}, loop ${trace.period}`
      : `Stops after ${trace.preperiod} emitted digits`;

  const currentEquation = currentTransition
    ? `${example.base} × ${currentTransition.remainder} = ${currentTransition.digit} × ${example.denominator} + ${currentTransition.nextRemainder}`
    : trace.kind === 'terminating'
    ? `remainder 0 reached: the digit stream has nowhere left to go`
    : `the walk has closed its finite orbit and is ready to repeat`;

  return (
    <div className="rounded-[1.75rem] border border-stone-200 bg-linear-to-br from-white via-stone-50 to-amber-50/70 p-5 shadow-sm sm:p-6">
      <div className="flex flex-col gap-5 xl:flex-row xl:items-start xl:justify-between">
        <div className="max-w-2xl">
          <div className="text-xs font-bold uppercase tracking-[0.22em] text-stone-500">
            Orbit Outcome Primer
          </div>
          <h3 className="mt-2 text-xl font-serif font-semibold tracking-tight text-stone-900 sm:text-2xl">
            Three lawful outcomes of long division
          </h3>
          <p className="mt-3 max-w-2xl text-sm leading-relaxed text-stone-700 sm:text-base">
            This panel reads atlas claims <code>digit_periodicity</code> and{' '}
            <code>preperiod_from_base_factors</code> as motion. Each step uses
            the Euclidean rule <code>base × r = d × N + r&apos;</code>: the node is
            the current remainder, the glowing box is the emitted digit, and the
            loop structure decides whether the expansion repeats or terminates.
          </p>
          <p className="mt-3 max-w-2xl text-sm leading-relaxed text-stone-700">
            Unlike the prime-phase and linked-97 surfaces, this one earns its
            keep by showing the universal trichotomy side by side: pure periodic
            orbit, preperiod into a smaller core, and genuine termination at
            remainder <code>0</code>.
          </p>
        </div>

        <div className="grid gap-3 sm:grid-cols-3 xl:w-[28rem]">
          {orbitExamples.map((entry) => {
            const isActive = entry.key === exampleKey;
            return (
              <button
                key={entry.key}
                type="button"
                onClick={() => setExampleKey(entry.key)}
                className={`rounded-2xl border px-4 py-3 text-left transition-all ${
                  isActive
                    ? 'border-stone-900 bg-stone-900 text-stone-50 shadow-lg shadow-stone-300/40'
                    : 'border-stone-200 bg-white/80 text-stone-700 hover:border-stone-400 hover:bg-white'
                }`}
              >
                <div className="text-xs font-semibold uppercase tracking-[0.18em] opacity-70">
                  {entry.theme}
                </div>
                <div className="mt-1 text-lg font-serif font-semibold">{entry.label}</div>
                <div className="mt-2 text-sm leading-relaxed opacity-85">{entry.summary}</div>
              </button>
            );
          })}
        </div>
      </div>

      <div className="mt-6 grid gap-6 xl:grid-cols-[1.2fr_0.8fr]">
        <div className="rounded-[1.5rem] border border-stone-200 bg-white/90 p-4">
          <div className="flex flex-wrap items-center justify-between gap-3">
            <div className="flex flex-wrap items-center gap-3">
              <span className="text-lg font-serif font-semibold text-stone-900">
                {example.label} in base {example.base}
              </span>
              <span className={`rounded-full px-3 py-1 text-xs font-bold uppercase tracking-wide ${kindPillStyles[trace.kind]}`}>
                {trace.kind === 'pure-periodic'
                  ? 'Pure periodic orbit'
                  : trace.kind === 'preperiodic'
                  ? 'Preperiod + orbit'
                  : 'Terminates at 0'}
              </span>
            </div>

            <div className="flex flex-wrap items-center gap-2">
              <button
                type="button"
                onClick={() => setIsPlaying((value) => !value)}
                className="rounded-full border border-stone-300 px-3 py-1.5 text-sm font-semibold text-stone-700 transition-colors hover:bg-stone-100"
              >
                {isPlaying ? 'Pause' : step >= maxStep ? 'Replay' : 'Play'}
              </button>
              <button
                type="button"
                onClick={() => {
                  setIsPlaying(false);
                  setStep((value) => Math.min(value + 1, maxStep));
                }}
                className="rounded-full border border-stone-300 px-3 py-1.5 text-sm font-semibold text-stone-700 transition-colors hover:bg-stone-100"
              >
                Step
              </button>
              <button
                type="button"
                onClick={() => {
                  setIsPlaying(false);
                  setStep(0);
                }}
                className="rounded-full border border-stone-300 px-3 py-1.5 text-sm font-semibold text-stone-700 transition-colors hover:bg-stone-100"
              >
                Reset
              </button>
              <label className="flex items-center gap-2 rounded-full border border-stone-300 px-3 py-1.5 text-sm text-stone-700">
                <span>Speed</span>
                <input
                  type="range"
                  min={300}
                  max={1400}
                  step={100}
                  value={speedMs}
                  onChange={(event) => setSpeedMs(Number(event.target.value))}
                  className="w-20 accent-stone-800"
                />
              </label>
            </div>
          </div>

          <div className="mt-4 grid gap-5 lg:grid-cols-[1fr_0.95fr]">
            <div className="rounded-[1.25rem] border border-stone-200 bg-linear-to-b from-stone-50 to-white p-3">
              <svg viewBox="0 0 200 200" className="w-full">
                <defs>
                  <marker
                    id={`orbit-arrow-${example.key}`}
                    markerWidth="8"
                    markerHeight="8"
                    refX="6"
                    refY="4"
                    orient="auto"
                  >
                    <path d="M 0 0 L 8 4 L 0 8 z" fill="#57534e" />
                  </marker>
                  <filter id={`orbit-glow-${example.key}`} x="-50%" y="-50%" width="200%" height="200%">
                    <feDropShadow dx="0" dy="0" stdDeviation="2.5" floodColor="#0f766e" floodOpacity="0.35" />
                  </filter>
                </defs>

                {trace.kind !== 'terminating' ? (
                  <circle
                    cx="100"
                    cy="100"
                    r="76"
                    fill="none"
                    stroke="#e7e5e4"
                    strokeDasharray="4 6"
                    strokeWidth="1.5"
                  />
                ) : (
                  <>
                    <circle
                      cx="100"
                      cy="88"
                      r="72"
                      fill="none"
                      stroke="#e7e5e4"
                      strokeDasharray="4 6"
                      strokeWidth="1.5"
                    />
                    <text
                      x="100"
                      y="154"
                      textAnchor="middle"
                      className="fill-stone-400 text-[10px] font-semibold uppercase tracking-[0.16em]"
                    >
                      terminal sink
                    </text>
                  </>
                )}

                {trace.steps.map((entry, index) => {
                  const path = edgePath(entry.remainder, entry.nextRemainder, positions, nodeRadius);
                  const isVisited = index < step;
                  const isCurrent = index === step;
                  return (
                    <path
                      key={`${entry.remainder}-${entry.nextRemainder}-${index}`}
                      d={path}
                      fill="none"
                      stroke={isVisited ? '#0f766e' : '#a8a29e'}
                      strokeWidth={isCurrent ? 4 : isVisited ? 3 : 2}
                      strokeLinecap="round"
                      strokeLinejoin="round"
                      filter={isCurrent ? `url(#orbit-glow-${example.key})` : undefined}
                      markerEnd={entry.remainder === entry.nextRemainder ? undefined : `url(#orbit-arrow-${example.key})`}
                      opacity={isVisited || isCurrent ? 1 : 0.45}
                    />
                  );
                })}

                {Array.from(positions.entries()).map(([state, point]) => {
                  const isZero = state === 0;
                  const isVisited =
                    state === 0
                      ? step >= maxStep && trace.kind === 'terminating'
                      : trace.steps.slice(0, step).some(
                          (entry) => entry.remainder === state || entry.nextRemainder === state,
                        );
                  const isCurrent = state === currentRemainder;
                  const isLoopState =
                    !isZero &&
                    trace.kind !== 'terminating' &&
                    trace.steps
                      .slice(trace.preperiod)
                      .some((entry) => entry.remainder === state || entry.nextRemainder === state);

                  return (
                    <g key={state}>
                      <circle
                        cx={point.x}
                        cy={point.y}
                        r={isZero ? 15 : nodeRadius}
                        fill={
                          isZero
                            ? isVisited
                              ? '#fb7185'
                              : '#ffe4e6'
                            : isCurrent
                            ? '#0f766e'
                            : isVisited
                            ? '#99f6e4'
                            : '#fafaf9'
                        }
                        stroke={
                          isZero ? '#e11d48' : isLoopState ? '#14b8a6' : '#78716c'
                        }
                        strokeWidth={isCurrent ? 3 : 2}
                        filter={isCurrent ? `url(#orbit-glow-${example.key})` : undefined}
                      />
                      <text
                        x={point.x}
                        y={point.y + 1}
                        textAnchor="middle"
                        dominantBaseline="middle"
                        className={`text-[11px] font-mono font-semibold ${
                          isCurrent
                            ? 'fill-white'
                            : isZero
                            ? 'fill-rose-700'
                            : 'fill-stone-700'
                        }`}
                      >
                        {state}
                      </text>
                    </g>
                  );
                })}
              </svg>
            </div>

            <div className="space-y-4">
              <div className="rounded-[1.25rem] border border-stone-200 bg-stone-50 p-4">
                <div className="text-xs font-bold uppercase tracking-[0.18em] text-stone-500">
                  Digit Emission
                </div>
                <div className="mt-3 flex flex-wrap gap-2">
                  {trace.steps.map((entry, index) => {
                    const isEmitted = index < step;
                    const isCurrent = index === step - 1;
                    return (
                      <div
                        key={`${entry.index}-${entry.digit}`}
                        className={`flex h-11 w-11 items-center justify-center rounded-xl border text-lg font-mono font-semibold transition-all ${
                          isCurrent
                            ? 'border-teal-700 bg-teal-700 text-white shadow-lg shadow-teal-700/25'
                            : isEmitted
                            ? 'border-teal-200 bg-teal-50 text-teal-800'
                            : 'border-stone-200 bg-white text-stone-400'
                        }`}
                      >
                        {formatDigit(entry.digit)}
                      </div>
                    );
                  })}
                </div>
                <div className="mt-4 rounded-2xl bg-white px-4 py-3 font-mono text-sm text-stone-700 shadow-sm">
                  {emittedDigits.length > 0 ? `0.${emittedDigits.map(formatDigit).join('')}` : '0.'}
                  {trace.kind !== 'terminating' && step >= maxStep ? '…' : ''}
                </div>
              </div>

              <div className="rounded-[1.25rem] border border-stone-200 bg-white p-4">
                <div className="flex flex-wrap items-center justify-between gap-2">
                  <div className="text-xs font-bold uppercase tracking-[0.18em] text-stone-500">
                    Current Law
                  </div>
                  <div className="rounded-full bg-stone-100 px-3 py-1 text-xs font-semibold text-stone-700">
                    {summaryLabel}
                  </div>
                </div>
                <div className="mt-3 font-mono text-sm leading-relaxed text-stone-800">
                  {currentEquation}
                </div>
                <p className="mt-3 text-sm leading-relaxed text-stone-700">
                  {example.summary}
                </p>
                <div className="mt-4 grid gap-3 sm:grid-cols-2">
                  <div className="rounded-2xl bg-stone-50 p-3">
                    <div className="text-xs font-bold uppercase tracking-[0.16em] text-stone-500">
                      Base factors
                    </div>
                    <div className="mt-2 font-mono text-sm text-stone-800">
                      {trace.basePrimeFactors.join(', ')}
                    </div>
                  </div>
                  <div className="rounded-2xl bg-stone-50 p-3">
                    <div className="text-xs font-bold uppercase tracking-[0.16em] text-stone-500">
                      Stripped core M
                    </div>
                    <div className="mt-2 font-mono text-sm text-stone-800">
                      {trace.strippedCore}
                    </div>
                  </div>
                </div>
              </div>
            </div>
          </div>
        </div>

        <aside className="rounded-[1.5rem] border border-stone-200 bg-white/90 p-4">
          <div className="text-xs font-bold uppercase tracking-[0.18em] text-stone-500">
            Why Keep This
          </div>
          <div className="mt-4 space-y-4 text-sm leading-relaxed text-stone-700">
            <p>
              When the denominator is coprime to the base, remainder <code>0</code> is not part of the
              moving system. The walk is forced to stay among nonzero states, so once a state repeats,
              the future repeats with it.
            </p>
            <p>
              If the denominator carries base factors, those factors can create either a short runway
              into a smaller repeating core, as in <code>1/6</code>, or a direct fall into <code>0</code>,
              as in <code>1/8</code>.
            </p>
            <p>
              That is the sense in which the non-terminating cases are “too lawful”: not drifting,
              but cycling inside a finite rule where no legal move leads to termination.
            </p>
          </div>

          <div className="mt-5 rounded-2xl border border-stone-200 bg-stone-50 p-4">
            <div className="text-xs font-bold uppercase tracking-[0.16em] text-stone-500">
              Repo Anchors
            </div>
            <div className="mt-3 space-y-2">
              <code className="block rounded bg-white px-3 py-2 text-xs text-stone-600">
                docs/PROOF_STATUS_ATLAS.md
              </code>
              <code className="block rounded bg-white px-3 py-2 text-xs text-stone-600">
                docs/EXPOSITORY_NOTE.md
              </code>
              <code className="block rounded bg-white px-3 py-2 text-xs text-stone-600">
                python -m bridge_reptends.examples.prime_19
              </code>
              <code className="block rounded bg-white px-3 py-2 text-xs text-stone-600">
                python -m bridge_reptends.examples.backwards
              </code>
            </div>
          </div>
        </aside>
      </div>
    </div>
  );
};

export default LawfulOrbitExplorer;
