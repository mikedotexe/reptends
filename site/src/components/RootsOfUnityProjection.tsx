import { useEffect, useEffectEvent, useMemo, useState } from 'react';
import { multiplicativeOrder } from '../lib/math';
import {
  buildDiscreteLogTable,
  pathFromPoints,
  pointOnUnitCircle,
  primitiveRoots,
} from '../lib/phaseGeometry';

interface ExampleConfig {
  key: string;
  label: string;
  prime: number;
  base: number;
  summary: string;
}

interface OrbitRow {
  index: number;
  remainder: number;
  exponent: number;
  digit: number;
  nextRemainder: number;
  nextExponent: number;
}

interface ProjectionData {
  example: ExampleConfig;
  primitiveRoots: number[];
  generator: number;
  residueByExponent: number[];
  exponentByResidue: Map<number, number>;
  rows: OrbitRow[];
  phaseStep: number;
  orbitLength: number;
}

const examples: ExampleConfig[] = [
  {
    key: '19',
    label: '1/19',
    prime: 19,
    base: 10,
    summary:
      'A compact full reptend case: eighteen nonzero remainders, with the full orbit visible at a human scale.',
  },
  {
    key: '97',
    label: '1/97',
    prime: 97,
    base: 10,
    summary:
      'The canonical bridge example at much higher resolution: ninety-six phases, still governed by the same rigid law.',
  },
];

function gcd(a: number, b: number): number {
  let x = Math.abs(a);
  let y = Math.abs(b);
  while (y !== 0) {
    const t = x % y;
    x = y;
    y = t;
  }
  return x;
}

function buildProjectionData(example: ExampleConfig, generator: number): ProjectionData {
  const primitiveRootList = primitiveRoots(example.prime);
  const { residueByExponent, exponentByResidue } = buildDiscreteLogTable(generator, example.prime);
  const orbitLength = multiplicativeOrder(example.base, example.prime);
  const phaseStep = exponentByResidue.get(example.base)!;
  const rows: OrbitRow[] = [];
  let remainder = 1;

  for (let index = 0; index < orbitLength; index++) {
    const digit = Math.floor((example.base * remainder) / example.prime);
    const nextRemainder = (example.base * remainder) % example.prime;
    rows.push({
      index,
      remainder,
      exponent: exponentByResidue.get(remainder)!,
      digit,
      nextRemainder,
      nextExponent: exponentByResidue.get(nextRemainder)!,
    });
    remainder = nextRemainder;
  }

  return {
    example,
    primitiveRoots: primitiveRootList,
    generator,
    residueByExponent,
    exponentByResidue,
    rows,
    phaseStep,
    orbitLength,
  };
}

const RootsOfUnityProjection = () => {
  const [exampleKey, setExampleKey] = useState(examples[0].key);
  const [generatorMode, setGeneratorMode] = useState<'base' | 'smallest'>('base');
  const [step, setStep] = useState(0);
  const [isPlaying, setIsPlaying] = useState(true);
  const [speedMs, setSpeedMs] = useState(850);

  const example = examples.find((entry) => entry.key === exampleKey) ?? examples[0];
  const smallestPrimitiveRoot = useMemo(() => primitiveRoots(example.prime)[0], [example.prime]);
  const selectedGenerator = generatorMode === 'base' ? example.base : smallestPrimitiveRoot;
  const data = useMemo(
    () => buildProjectionData(example, selectedGenerator),
    [example, selectedGenerator],
  );

  const currentRemainder =
    step === 0 ? 1 : data.rows[Math.min(step, data.rows.length) - 1]?.nextRemainder ?? 1;
  const currentExponent = data.exponentByResidue.get(currentRemainder) ?? 0;
  const currentRow = step < data.rows.length ? data.rows[step] : null;
  const emittedDigits = data.rows.slice(0, step).map((row) => row.digit);
  const showAllResidueLabels = example.prime <= 19;
  const tickStep = example.prime <= 19 ? 3 : 12;
  const currentPoint = pointOnUnitCircle(currentExponent, example.prime - 1, 92);
  const visitedResidues = new Set<number>([1]);
  for (const row of data.rows.slice(0, step)) {
    visitedResidues.add(row.remainder);
    visitedResidues.add(row.nextRemainder);
  }

  const orbitPoints = [pointOnUnitCircle(0, example.prime - 1, 92)];
  for (const row of data.rows.slice(0, step)) {
    orbitPoints.push(pointOnUnitCircle(row.nextExponent, example.prime - 1, 92));
  }

  const qrPoints = data.residueByExponent
    .filter((_, exponent) => exponent % 2 === 0)
    .map((residue) => {
      const exponent = data.exponentByResidue.get(residue) ?? 0;
      return pointOnUnitCircle(exponent, example.prime - 1, 92);
    });

  const advance = useEffectEvent(() => {
    setStep((current) => {
      if (current >= data.rows.length) {
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
    setIsPlaying(true);
  }, [exampleKey, generatorMode]);

  const currentLaw = currentRow
    ? `e_${currentRow.index + 1} = e_${currentRow.index} + ${data.phaseStep} (mod ${example.prime - 1})`
    : `the orbit has completed one full phase walk and is ready to repeat`;

  const currentDivision = currentRow
    ? `${example.base} × ${currentRow.remainder} = ${currentRow.digit} × ${example.prime} + ${currentRow.nextRemainder}`
    : `${example.base} acts as a rigid phase step on the unit circle`;

  const phaseFraction = `${data.phaseStep}/${example.prime - 1}`;
  const reducedPhase = (() => {
    const divisor = gcd(data.phaseStep, example.prime - 1);
    return `${data.phaseStep / divisor}/${(example.prime - 1) / divisor}`;
  })();

  return (
    <div className="rounded-[1.75rem] border border-stone-200 bg-linear-to-br from-white via-stone-50 to-sky-50/70 p-5 shadow-sm sm:p-6">
      <div className="flex flex-col gap-5 xl:flex-row xl:items-start xl:justify-between">
        <div className="max-w-3xl">
          <div className="text-xs font-bold uppercase tracking-[0.22em] text-stone-500">
            Geometry Surface
          </div>
          <h3 className="mt-2 text-xl font-serif font-semibold tracking-tight text-stone-900 sm:text-2xl">
            Roots-of-unity projection of the remainder orbit
          </h3>
          <p className="mt-3 text-sm leading-relaxed text-stone-700 sm:text-base">
            Using the classical cyclicity of <code>(Z/pZ)×</code>, choose a primitive root{' '}
            <code>g</code>, write each nonzero remainder as <code>r = g^e</code>, and project it to{' '}
            <code>exp(2πie/(p-1))</code>. In this coordinate, multiplication by the base becomes a rigid
            phase shift. Changing <code>g</code> changes the chart, not the underlying orbit law.
          </p>
        </div>

        <div className="grid gap-3 sm:grid-cols-2 xl:w-[28rem]">
          {examples.map((entry) => {
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
                  base 10
                </div>
                <div className="mt-1 text-lg font-serif font-semibold">{entry.label}</div>
                <div className="mt-2 text-sm leading-relaxed opacity-85">{entry.summary}</div>
              </button>
            );
          })}
        </div>
      </div>

      <div className="mt-5 flex flex-wrap items-center gap-3">
        <div className="text-xs font-bold uppercase tracking-[0.18em] text-stone-500">
          Primitive-root coordinate
        </div>
        <button
          type="button"
          onClick={() => setGeneratorMode('base')}
          className={`rounded-full border px-3 py-1.5 text-sm font-semibold transition-colors ${
            generatorMode === 'base'
              ? 'border-sky-700 bg-sky-700 text-white'
              : 'border-stone-300 bg-white text-stone-700 hover:bg-stone-100'
          }`}
        >
          g = {example.base} (the base)
        </button>
        <button
          type="button"
          onClick={() => setGeneratorMode('smallest')}
          className={`rounded-full border px-3 py-1.5 text-sm font-semibold transition-colors ${
            generatorMode === 'smallest'
              ? 'border-sky-700 bg-sky-700 text-white'
              : 'border-stone-300 bg-white text-stone-700 hover:bg-stone-100'
          }`}
        >
          g = {smallestPrimitiveRoot} (smallest primitive root)
        </button>
        <div className="rounded-full bg-stone-100 px-3 py-1.5 text-sm text-stone-700">
          phase step s = log_g(10) = {data.phaseStep}
        </div>
      </div>

      <div className="mt-6 grid gap-6 xl:grid-cols-[1.2fr_0.8fr]">
        <div className="rounded-[1.5rem] border border-stone-200 bg-white/90 p-4">
          <div className="flex flex-wrap items-center justify-between gap-3">
            <div className="flex flex-wrap items-center gap-3">
              <div className="text-sm font-semibold uppercase tracking-[0.16em] text-stone-500">
                Unit-circle orbit
              </div>
              <div className="rounded-full bg-sky-100 px-3 py-1 text-xs font-bold uppercase tracking-wide text-sky-900">
                preserves cyclic order after choosing g
              </div>
            </div>

            <div className="flex flex-wrap items-center gap-2">
              <button
                type="button"
                onClick={() => {
                  if (step >= data.rows.length) {
                    setStep(0);
                    setIsPlaying(true);
                    return;
                  }
                  setIsPlaying((value) => !value);
                }}
                className="rounded-full border border-stone-300 px-3 py-1.5 text-sm font-semibold text-stone-700 transition-colors hover:bg-stone-100"
              >
                {isPlaying ? 'Pause' : step >= data.rows.length ? 'Replay' : 'Play'}
              </button>
              <button
                type="button"
                onClick={() => {
                  setIsPlaying(false);
                  setStep((current) => Math.min(current + 1, data.rows.length));
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
                  min={250}
                  max={1300}
                  step={100}
                  value={speedMs}
                  onChange={(event) => setSpeedMs(Number(event.target.value))}
                  className="w-20 accent-stone-800"
                />
              </label>
            </div>
          </div>

          <div className="mt-4 rounded-[1.25rem] border border-stone-200 bg-linear-to-b from-stone-50 to-white p-3">
            <svg viewBox="0 0 280 280" className="w-full">
              <defs>
                <filter id={`phase-glow-${example.key}`} x="-50%" y="-50%" width="200%" height="200%">
                  <feDropShadow dx="0" dy="0" stdDeviation="2.6" floodColor="#0369a1" floodOpacity="0.35" />
                </filter>
              </defs>

              <circle cx="140" cy="140" r="100" fill="none" stroke="#d6d3d1" strokeWidth="1.5" />
              <circle cx="140" cy="140" r="92" fill="none" stroke="#f5f5f4" strokeWidth="20" />

              {Array.from({ length: example.prime - 1 }, (_, exponent) => exponent)
                .filter((exponent) => exponent % tickStep === 0)
                .map((exponent) => {
                  const inner = pointOnUnitCircle(exponent, example.prime - 1, 104);
                  const outer = pointOnUnitCircle(exponent, example.prime - 1, 114);
                  const label = pointOnUnitCircle(exponent, example.prime - 1, 125);
                  return (
                    <g key={`tick-${exponent}`}>
                      <line
                        x1={inner.x}
                        y1={inner.y}
                        x2={outer.x}
                        y2={outer.y}
                        stroke="#a8a29e"
                        strokeWidth="1"
                      />
                      <text
                        x={label.x}
                        y={label.y + 3}
                        textAnchor="middle"
                        className="fill-stone-400 text-[9px] font-mono"
                      >
                        {exponent}
                      </text>
                    </g>
                  );
                })}

              <path
                d={pathFromPoints(qrPoints, true)}
                fill="rgba(14, 165, 233, 0.06)"
                stroke="#7dd3fc"
                strokeWidth="1.5"
                strokeDasharray="3 4"
              />

              {orbitPoints.length > 1 ? (
                <path
                  d={pathFromPoints(orbitPoints)}
                  fill="none"
                  stroke="#1f2937"
                  strokeWidth={example.prime <= 19 ? 2.6 : 1.8}
                  strokeLinecap="round"
                  strokeLinejoin="round"
                  opacity={0.78}
                />
              ) : null}

              <line
                x1="140"
                y1="140"
                x2={currentPoint.x}
                y2={currentPoint.y}
                stroke="#0369a1"
                strokeWidth="2"
                strokeLinecap="round"
                filter={`url(#phase-glow-${example.key})`}
              />

              {data.residueByExponent.map((residue, exponent) => {
                const point = pointOnUnitCircle(exponent, example.prime - 1, 92);
                const isQR = exponent % 2 === 0;
                const isVisited = visitedResidues.has(residue);
                const isCurrent = residue === currentRemainder;
                const isBase = residue === example.base;
                const shouldLabel =
                  showAllResidueLabels || isCurrent || residue === 1 || isBase;

                return (
                  <g key={`residue-${residue}`}>
                    <circle
                      cx={point.x}
                      cy={point.y}
                      r={isCurrent ? 8 : isVisited ? 5.5 : 4}
                      fill={
                        isCurrent
                          ? '#0369a1'
                          : isQR
                          ? isVisited
                            ? '#67e8f9'
                            : '#cffafe'
                          : isVisited
                          ? '#fdba74'
                          : '#fed7aa'
                      }
                      stroke={isCurrent ? '#0c4a6e' : isQR ? '#0891b2' : '#ea580c'}
                      strokeWidth={isCurrent ? 2.4 : 1.2}
                      filter={isCurrent ? `url(#phase-glow-${example.key})` : undefined}
                    />

                    {shouldLabel ? (
                      <text
                        x={point.x}
                        y={point.y + (showAllResidueLabels ? 15 : -11)}
                        textAnchor="middle"
                        className={`text-[9px] font-mono font-semibold ${
                          isCurrent ? 'fill-sky-800' : 'fill-stone-500'
                        }`}
                      >
                        {residue}
                      </text>
                    ) : null}
                  </g>
                );
              })}

              <circle cx="140" cy="140" r="13" fill="white" stroke="#d6d3d1" strokeWidth="1.5" />
              <text
                x="140"
                y="144"
                textAnchor="middle"
                className="fill-stone-500 text-[10px] font-semibold uppercase tracking-[0.16em]"
              >
                g={selectedGenerator}
              </text>
            </svg>
          </div>

          <div className="mt-4 grid gap-3 sm:grid-cols-3">
            <div className="rounded-2xl border border-stone-200 bg-stone-50 p-3">
              <div className="text-xs font-bold uppercase tracking-[0.16em] text-stone-500">
                Current remainder
              </div>
              <div className="mt-2 font-mono text-lg text-stone-900">{currentRemainder}</div>
            </div>
            <div className="rounded-2xl border border-stone-200 bg-stone-50 p-3">
              <div className="text-xs font-bold uppercase tracking-[0.16em] text-stone-500">
                Current exponent
              </div>
              <div className="mt-2 font-mono text-lg text-stone-900">{currentExponent}</div>
            </div>
            <div className="rounded-2xl border border-stone-200 bg-stone-50 p-3">
              <div className="text-xs font-bold uppercase tracking-[0.16em] text-stone-500">
                Digits emitted
              </div>
              <div className="mt-2 font-mono text-lg text-stone-900">{step}</div>
            </div>
          </div>
        </div>

        <aside className="space-y-4">
          <div className="rounded-[1.5rem] border border-stone-200 bg-white/90 p-4">
            <div className="text-xs font-bold uppercase tracking-[0.18em] text-stone-500">
              Current law
            </div>
            <div className="mt-3 rounded-2xl bg-stone-50 p-4">
              <div className="font-mono text-sm leading-relaxed text-stone-800">{currentLaw}</div>
              <div className="mt-2 font-mono text-sm leading-relaxed text-stone-800">
                {currentDivision}
              </div>
            </div>
            <div className="mt-4 rounded-2xl bg-sky-50 px-4 py-3">
              <div className="text-xs font-bold uppercase tracking-[0.16em] text-sky-800">
                Digit prefix
              </div>
              <div className="mt-2 font-mono text-sm text-sky-950">
                {emittedDigits.length > 0 ? `0.${emittedDigits.join('')}` : '0.'}
                {step >= data.rows.length ? '…' : ''}
              </div>
            </div>
          </div>

          <div className="rounded-[1.5rem] border border-stone-200 bg-white/90 p-4">
            <div className="text-xs font-bold uppercase tracking-[0.18em] text-stone-500">
              Preserved signal
            </div>
            <div className="mt-3 space-y-3 text-sm leading-relaxed text-stone-700">
              <p>
                <span className="font-semibold text-stone-900">Phase law.</span> In this chart, the
                orbit is the arithmetic progression <code>e ↦ e + s</code> with{' '}
                <code>s = {data.phaseStep}</code>.
              </p>
              <p>
                <span className="font-semibold text-stone-900">QR parity.</span> Even exponents are the
                quadratic-residue subgroup, so when <code>s</code> is odd the orbit alternates QR and NQR.
              </p>
              <p>
                <span className="font-semibold text-stone-900">Order.</span> The orbit length is{' '}
                <code>(p-1)/gcd(p-1, s) = {data.orbitLength}</code>.
              </p>
            </div>
          </div>

          <div className="rounded-[1.5rem] border border-stone-200 bg-white/90 p-4 text-sm leading-relaxed text-stone-700">
            <div className="text-xs font-bold uppercase tracking-[0.18em] text-stone-500">
              Coordinate note
            </div>
            <p className="mt-3">
              With <code>g = 10</code>, the base step is one unit of phase, so the orbit becomes a
              consecutive walk around the circle. With <code>g = {smallestPrimitiveRoot}</code>, the same
              digits ride a different star polygon because the step is <code>{phaseFraction}</code> of a
              turn, reducing to <code>{reducedPhase}</code>.
            </p>
            <p className="mt-3">
              That is the useful signal: the picture is choice-dependent, but the phase law, subgroup
              parity, and orbit length survive the change of primitive-root chart.
            </p>
          </div>
        </aside>
      </div>
    </div>
  );
};

export default RootsOfUnityProjection;
