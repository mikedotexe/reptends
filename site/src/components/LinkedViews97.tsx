import { useEffect, useEffectEvent, useMemo, useState } from 'react';
import {
  PRIME97_BRIDGE_EXAMPLE,
  buildBridgeBlocks,
  formatBlock,
} from './BridgeCarryExplorer97';
import {
  type Point,
  buildDiscreteLogTable,
  pathFromPoints,
  pointOnUnitCircle,
  primitiveRoots,
} from '../lib/phaseGeometry';

type GeneratorMode = 'base' | 'smallest';

function pointOnOrbitRing(index: number, total: number, radius: number): Point {
  const angle = -Math.PI / 2 + (2 * Math.PI * index) / total;
  return {
    x: 120 + Math.cos(angle) * radius,
    y: 120 + Math.sin(angle) * radius,
  };
}

interface LinkedCellProps {
  activeIndex: number;
  index: number;
  label: string;
  tone: 'raw' | 'carry' | 'visible' | 'actual';
  onSelect: (index: number) => void;
}

const linkedCellStyles: Record<LinkedCellProps['tone'], { idle: string; active: string }> = {
  raw: {
    idle: 'border-stone-200 bg-white text-stone-700 hover:border-amber-300',
    active: 'border-amber-500 bg-amber-100 text-amber-950 shadow-sm shadow-amber-200/70',
  },
  carry: {
    idle: 'border-stone-200 bg-teal-50/70 text-teal-800 hover:border-teal-300',
    active: 'border-teal-500 bg-teal-600 text-white shadow-sm shadow-teal-300/50',
  },
  visible: {
    idle: 'border-stone-200 bg-emerald-50/70 text-emerald-900 hover:border-emerald-300',
    active: 'border-emerald-500 bg-emerald-600 text-white shadow-sm shadow-emerald-300/50',
  },
  actual: {
    idle: 'border-stone-200 bg-indigo-50/70 text-indigo-900 hover:border-indigo-300',
    active: 'border-indigo-500 bg-indigo-600 text-white shadow-sm shadow-indigo-300/50',
  },
};

const LinkedCell = ({ activeIndex, index, label, tone, onSelect }: LinkedCellProps) => {
  const isActive = activeIndex === index;
  const styles = linkedCellStyles[tone];

  return (
    <button
      type="button"
      onClick={() => onSelect(index)}
      className={`flex min-w-[5.3rem] flex-col rounded-xl border px-3 py-2 text-center font-mono text-sm transition-all ${
        isActive ? styles.active : styles.idle
      }`}
    >
      <span className="text-[10px] uppercase tracking-[0.18em] opacity-60">j={index}</span>
      <span className="mt-1 font-semibold">{label}</span>
    </button>
  );
};

const LinkedViews97 = () => {
  const blocks = useMemo(() => buildBridgeBlocks(), []);
  const [activeIndex, setActiveIndex] = useState(0);
  const [isPlaying, setIsPlaying] = useState(false);
  const [speedMs, setSpeedMs] = useState(900);
  const [generatorMode, setGeneratorMode] = useState<GeneratorMode>('base');

  const primitiveRootList = useMemo(
    () => primitiveRoots(PRIME97_BRIDGE_EXAMPLE.modulus),
    [],
  );
  const selectedGenerator =
    generatorMode === 'base' ? PRIME97_BRIDGE_EXAMPLE.base : primitiveRootList[0];
  const exponentByResidue = useMemo(
    () => buildDiscreteLogTable(selectedGenerator, PRIME97_BRIDGE_EXAMPLE.modulus).exponentByResidue,
    [selectedGenerator],
  );
  const base10PhaseTable = useMemo(
    () =>
      buildDiscreteLogTable(
        PRIME97_BRIDGE_EXAMPLE.base,
        PRIME97_BRIDGE_EXAMPLE.modulus,
      ).exponentByResidue,
    [],
  );
  const phaseStep = exponentByResidue.get(PRIME97_BRIDGE_EXAMPLE.blockBase % PRIME97_BRIDGE_EXAMPLE.modulus) ?? 0;
  const qrPhaseStep = base10PhaseTable.get(
    PRIME97_BRIDGE_EXAMPLE.blockBase % PRIME97_BRIDGE_EXAMPLE.modulus,
  ) ?? 0;

  const current = blocks[activeIndex] ?? blocks[0];
  const firstIncomingCarryIndex = blocks.find((block) => block.incoming > 0)?.index ?? null;
  const digitPrefix = blocks
    .slice(0, activeIndex + 1)
    .map((block) => formatBlock(block.actual, PRIME97_BRIDGE_EXAMPLE.blockWidth))
    .join('');

  const phaseRows = blocks.map((block) => ({
    ...block,
    exponent: exponentByResidue.get(block.remainder) ?? 0,
    nextExponent: exponentByResidue.get(block.nextRemainder) ?? 0,
  }));

  const fullOrbitExponents = Array.from({ length: PRIME97_BRIDGE_EXAMPLE.period }, (_, index) =>
    (index * phaseStep) % (PRIME97_BRIDGE_EXAMPLE.modulus - 1),
  );
  const fullOrbitPoints = fullOrbitExponents.map((exponent) =>
    pointOnUnitCircle(exponent, PRIME97_BRIDGE_EXAMPLE.modulus - 1, 92),
  );
  const prefixPhasePoints = phaseRows
    .slice(0, activeIndex + 1)
    .map((row) => pointOnUnitCircle(row.exponent, PRIME97_BRIDGE_EXAMPLE.modulus - 1, 92));
  const currentPhasePoint = pointOnUnitCircle(
    phaseRows[activeIndex]?.exponent ?? 0,
    PRIME97_BRIDGE_EXAMPLE.modulus - 1,
    92,
  );
  const currentQrExponent = base10PhaseTable.get(current.remainder) ?? 0;
  const currentThresholdPower = current.raw * PRIME97_BRIDGE_EXAMPLE.remainder;
  const carryThreshold = PRIME97_BRIDGE_EXAMPLE.blockBase - PRIME97_BRIDGE_EXAMPLE.remainder;
  const thresholdReached = currentThresholdPower >= carryThreshold;

  const advance = useEffectEvent(() => {
    setActiveIndex((index) => {
      if (index >= blocks.length - 1) {
        setIsPlaying(false);
        return index;
      }

      return index + 1;
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

  const currentEquation = `d_${current.index} = ${current.raw} + ${current.incoming} - ${current.leftTransfer} = ${current.visible}`;
  const currentRemainderEquation = `${PRIME97_BRIDGE_EXAMPLE.blockBase} × ${current.remainder} = ${current.actual} × ${PRIME97_BRIDGE_EXAMPLE.modulus} + ${current.nextRemainder}`;
  const currentPhaseEquation = `e_${current.index + 1} = e_${current.index} + ${phaseStep} (mod ${PRIME97_BRIDGE_EXAMPLE.modulus - 1})`;

  return (
    <div className="mb-6 rounded-[1.85rem] border border-stone-200 bg-linear-to-br from-white via-stone-50 to-cyan-50/60 p-5 shadow-sm sm:p-6">
      <div className="flex flex-col gap-5 xl:flex-row xl:items-start xl:justify-between">
        <div className="max-w-3xl">
          <div className="text-xs font-bold uppercase tracking-[0.22em] text-stone-500">
            Linked Views
          </div>
          <h3 className="mt-2 text-xl font-serif font-semibold tracking-tight text-stone-900 sm:text-2xl">
            One shared playhead through the 1/97 block machine
          </h3>
          <p className="mt-3 text-sm leading-relaxed text-stone-700 sm:text-base">
            This mode synchronizes three exact views of the same coordinate
            <code> (base, N, m, B, q, k) = (10, 97, 2, 100, 1, 3)</code>. The shared index
            <code> j </code> refers to a block step under <code>B = 100</code>, so the carry panel,
            the remainder orbit, and the roots-of-unity chart all refer to the same transition.
          </p>
          <p className="mt-3 text-sm leading-relaxed text-stone-700">
            Click any node or carry cell to scrub. The point here is not just pretty alignment; it is
            to make it obvious that “orbit law,” “phase law,” and “carry normalization” are three
            views of one lawful state update.
          </p>
        </div>

        <div className="rounded-[1.25rem] border border-stone-200 bg-white/90 p-4 shadow-sm xl:w-[28rem]">
          <div className="flex flex-wrap items-center gap-2">
            <button
              type="button"
              onClick={() => {
                if (activeIndex >= blocks.length - 1) {
                  setActiveIndex(0);
                  setIsPlaying(true);
                  return;
                }
                setIsPlaying((value) => !value);
              }}
              className="rounded-full border border-stone-300 px-3 py-1.5 text-sm font-semibold text-stone-700 transition-colors hover:bg-stone-100"
            >
              {isPlaying ? 'Pause' : activeIndex >= blocks.length - 1 ? 'Replay' : 'Play'}
            </button>
            <button
              type="button"
              onClick={() => {
                setIsPlaying(false);
                setActiveIndex((index) => Math.min(index + 1, blocks.length - 1));
              }}
              className="rounded-full border border-stone-300 px-3 py-1.5 text-sm font-semibold text-stone-700 transition-colors hover:bg-stone-100"
            >
              Step
            </button>
            <button
              type="button"
              onClick={() => {
                setIsPlaying(false);
                setActiveIndex(0);
              }}
              className="rounded-full border border-stone-300 px-3 py-1.5 text-sm font-semibold text-stone-700 transition-colors hover:bg-stone-100"
            >
              Reset
            </button>
            <label className="ml-auto flex items-center gap-2 rounded-full border border-stone-300 px-3 py-1.5 text-sm text-stone-700">
              <span>Speed</span>
              <input
                type="range"
                min={350}
                max={1300}
                step={100}
                value={speedMs}
                onChange={(event) => setSpeedMs(Number(event.target.value))}
                className="w-20 accent-stone-800"
              />
            </label>
          </div>

          <div className="mt-4 grid gap-3 sm:grid-cols-2">
            <div className="rounded-2xl bg-stone-50 p-3">
              <div className="text-xs font-bold uppercase tracking-[0.16em] text-stone-500">
                Shared block
              </div>
              <div className="mt-2 font-mono text-lg text-stone-900">j = {activeIndex}</div>
            </div>
            <div className="rounded-2xl bg-stone-50 p-3">
              <div className="text-xs font-bold uppercase tracking-[0.16em] text-stone-500">
                Current remainder
              </div>
              <div className="mt-2 font-mono text-lg text-stone-900">{current.remainder}</div>
            </div>
            <div className="rounded-2xl bg-stone-50 p-3 sm:col-span-2">
              <div className="text-xs font-bold uppercase tracking-[0.16em] text-stone-500">
                Visible prefix
              </div>
              <div className="mt-2 font-mono text-sm text-stone-900">0.{digitPrefix}…</div>
            </div>
          </div>

          <div className="mt-4 rounded-2xl border border-sky-100 bg-sky-50 p-4 text-sm leading-relaxed text-sky-950">
            <div className="text-xs font-bold uppercase tracking-[0.16em] text-sky-700">
              Phase And Threshold
            </div>
            <p className="mt-2">
              In the fixed <code>g = 10</code> coordinate, <code>log_g(100) = {qrPhaseStep}</code>, so
              the block orbit walks the even exponents only: the quadratic-residue subgroup.
            </p>
            <div className="mt-3 grid gap-3 sm:grid-cols-3">
              <div className="rounded-xl bg-white px-3 py-2">
                <div className="text-[10px] font-bold uppercase tracking-[0.16em] text-sky-700">
                  QR phase
                </div>
                <div className="mt-1 font-mono text-stone-900">e = {currentQrExponent}</div>
              </div>
              <div className="rounded-xl bg-white px-3 py-2">
                <div className="text-[10px] font-bold uppercase tracking-[0.16em] text-sky-700">
                  qk^(j+1)
                </div>
                <div className="mt-1 font-mono text-stone-900">{currentThresholdPower}</div>
              </div>
              <div className="rounded-xl bg-white px-3 py-2">
                <div className="text-[10px] font-bold uppercase tracking-[0.16em] text-sky-700">
                  B-k
                </div>
                <div className="mt-1 font-mono text-stone-900">{carryThreshold}</div>
              </div>
            </div>
            <p className="mt-3">
              {thresholdReached
                ? `At j = ${current.index}, the threshold has been crossed, so incoming carry is active (${current.incoming}).`
                : `At j = ${current.index}, the threshold has not been crossed yet, so the carry layer is still dormant.`}
            </p>
            {firstIncomingCarryIndex != null ? (
              <div className="mt-2 text-xs text-sky-800">
                First incoming carry occurs at <code>j = {firstIncomingCarryIndex}</code>.
              </div>
            ) : null}
          </div>
        </div>
      </div>

      <div className="mt-6 grid gap-6 xl:grid-cols-3">
        <article className="rounded-[1.5rem] border border-stone-200 bg-white/90 p-4">
          <div className="flex items-center justify-between gap-3">
            <div>
              <div className="text-xs font-bold uppercase tracking-[0.18em] text-stone-500">
                Orbit Order
              </div>
              <div className="mt-1 text-sm font-semibold text-stone-900">
                First 12 block remainders under B = 100
              </div>
            </div>
            <div className="rounded-full bg-amber-100 px-3 py-1 text-xs font-bold uppercase tracking-wide text-amber-900">
              preserves visit order
            </div>
          </div>

          <svg viewBox="0 0 240 240" className="mt-4 w-full">
            {phaseRows.map((row, index) => {
              const point = pointOnOrbitRing(index, phaseRows.length, 82);
              const nextPoint =
                index < phaseRows.length - 1
                  ? pointOnOrbitRing(index + 1, phaseRows.length, 82)
                  : null;
              const isVisited = index <= activeIndex;
              const isCurrent = index === activeIndex;

              return (
                <g key={`window-${row.index}`}>
                  {nextPoint ? (
                    <line
                      x1={point.x}
                      y1={point.y}
                      x2={nextPoint.x}
                      y2={nextPoint.y}
                      stroke={index < activeIndex ? '#0f766e' : '#d6d3d1'}
                      strokeWidth={index === activeIndex ? 3 : 2}
                      strokeLinecap="round"
                    />
                  ) : null}
                  <circle
                    cx={point.x}
                    cy={point.y}
                    r={isCurrent ? 13 : 11}
                    fill={isCurrent ? '#0f766e' : isVisited ? '#99f6e4' : '#fafaf9'}
                    stroke={isCurrent ? '#134e4a' : '#78716c'}
                    strokeWidth={isCurrent ? 2.5 : 1.4}
                    onClick={() => {
                      setIsPlaying(false);
                      setActiveIndex(index);
                    }}
                    className="cursor-pointer"
                  />
                  <text
                    x={point.x}
                    y={point.y + 1}
                    textAnchor="middle"
                    dominantBaseline="middle"
                    className={`text-[10px] font-mono font-semibold ${
                      isCurrent ? 'fill-white' : 'fill-stone-700'
                    }`}
                  >
                    {row.remainder}
                  </text>
                  <text
                    x={point.x}
                    y={point.y + 22}
                    textAnchor="middle"
                    className="fill-stone-400 text-[9px] font-mono"
                  >
                    j={row.index}
                  </text>
                </g>
              );
            })}

            <circle cx="120" cy="120" r="17" fill="white" stroke="#d6d3d1" strokeWidth="1.5" />
            <text
              x="120"
              y="124"
              textAnchor="middle"
              className="fill-stone-500 text-[10px] font-semibold uppercase tracking-[0.16em]"
            >
              B=100
            </text>
          </svg>
        </article>

        <article className="rounded-[1.5rem] border border-stone-200 bg-white/90 p-4">
          <div className="flex items-start justify-between gap-3">
            <div>
              <div className="text-xs font-bold uppercase tracking-[0.18em] text-stone-500">
                Roots Of Unity
              </div>
              <div className="mt-1 text-sm font-semibold text-stone-900">
                Same orbit in primitive-root coordinates
              </div>
            </div>
            <div className="rounded-full bg-sky-100 px-3 py-1 text-xs font-bold uppercase tracking-wide text-sky-900">
              preserves phase law
            </div>
          </div>

          <div className="mt-3 flex flex-wrap items-center gap-2">
            <button
              type="button"
              onClick={() => setGeneratorMode('base')}
              className={`rounded-full border px-3 py-1.5 text-sm font-semibold transition-colors ${
                generatorMode === 'base'
                  ? 'border-sky-700 bg-sky-700 text-white'
                  : 'border-stone-300 bg-white text-stone-700 hover:bg-stone-100'
              }`}
            >
              g = 10
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
              g = {primitiveRootList[0]}
            </button>
            <div className="rounded-full bg-stone-100 px-3 py-1.5 text-sm text-stone-700">
              log_g(100) = {phaseStep}
            </div>
          </div>

          <svg viewBox="0 0 280 280" className="mt-4 w-full">
            <circle cx="140" cy="140" r="100" fill="none" stroke="#d6d3d1" strokeWidth="1.5" />

            {Array.from({ length: PRIME97_BRIDGE_EXAMPLE.modulus - 1 }, (_, exponent) => exponent)
              .filter((exponent) => exponent % 12 === 0)
              .map((exponent) => {
                const inner = pointOnUnitCircle(exponent, PRIME97_BRIDGE_EXAMPLE.modulus - 1, 104);
                const outer = pointOnUnitCircle(exponent, PRIME97_BRIDGE_EXAMPLE.modulus - 1, 114);
                const label = pointOnUnitCircle(exponent, PRIME97_BRIDGE_EXAMPLE.modulus - 1, 124);
                return (
                  <g key={`phase-${exponent}`}>
                    <line x1={inner.x} y1={inner.y} x2={outer.x} y2={outer.y} stroke="#a8a29e" strokeWidth="1" />
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
              d={pathFromPoints(fullOrbitPoints, true)}
              fill="rgba(14, 165, 233, 0.05)"
              stroke="#bae6fd"
              strokeWidth="1.5"
              strokeDasharray="3 4"
            />

            {prefixPhasePoints.length > 1 ? (
              <path
                d={pathFromPoints(prefixPhasePoints)}
                fill="none"
                stroke="#0f172a"
                strokeWidth="2.2"
                strokeLinecap="round"
                strokeLinejoin="round"
              />
            ) : null}

            {phaseRows.map((row, index) => {
              const point = pointOnUnitCircle(row.exponent, PRIME97_BRIDGE_EXAMPLE.modulus - 1, 92);
              const isVisited = index <= activeIndex;
              const isCurrent = index === activeIndex;
              return (
                <g key={`phase-node-${row.index}`}>
                  <circle
                    cx={point.x}
                    cy={point.y}
                    r={isCurrent ? 8 : 5.5}
                    fill={isCurrent ? '#0369a1' : isVisited ? '#7dd3fc' : '#e0f2fe'}
                    stroke={isCurrent ? '#0c4a6e' : '#0369a1'}
                    strokeWidth={isCurrent ? 2.2 : 1.2}
                    onClick={() => {
                      setIsPlaying(false);
                      setActiveIndex(index);
                    }}
                    className="cursor-pointer"
                  />
                  {isCurrent ? (
                    <text
                      x={point.x}
                      y={point.y - 13}
                      textAnchor="middle"
                      className="fill-sky-800 text-[9px] font-mono font-semibold"
                    >
                      r={row.remainder}
                    </text>
                  ) : null}
                </g>
              );
            })}

            <line
              x1="140"
              y1="140"
              x2={currentPhasePoint.x}
              y2={currentPhasePoint.y}
              stroke="#0369a1"
              strokeWidth="2"
            />

            <circle cx="140" cy="140" r="16" fill="white" stroke="#d6d3d1" strokeWidth="1.5" />
            <text
              x="140"
              y="144"
              textAnchor="middle"
              className="fill-stone-500 text-[10px] font-semibold uppercase tracking-[0.16em]"
            >
              g={selectedGenerator}
            </text>
          </svg>
        </article>

        <article className="rounded-[1.5rem] border border-stone-200 bg-white/90 p-4">
          <div className="flex items-center justify-between gap-3">
            <div>
              <div className="text-xs font-bold uppercase tracking-[0.18em] text-stone-500">
                Carry Layer
              </div>
              <div className="mt-1 text-sm font-semibold text-stone-900">
                The same j highlighted in the block normalization
              </div>
            </div>
            <div className="rounded-full bg-emerald-100 px-3 py-1 text-xs font-bold uppercase tracking-wide text-emerald-900">
              preserves emitted block
            </div>
          </div>

          <div className="mt-4 space-y-3 overflow-x-auto pb-1">
            <div className="flex items-center gap-3">
              <div className="w-24 shrink-0 text-xs font-bold uppercase tracking-[0.16em] text-stone-500">
                Raw
              </div>
              <div className="flex gap-2">
                {blocks.map((block) => (
                  <LinkedCell
                    key={`linked-raw-${block.index}`}
                    activeIndex={activeIndex}
                    index={block.index}
                    label={String(block.raw)}
                    tone="raw"
                    onSelect={(index) => {
                      setIsPlaying(false);
                      setActiveIndex(index);
                    }}
                  />
                ))}
              </div>
            </div>

            <div className="flex items-center gap-3">
              <div className="w-24 shrink-0 text-xs font-bold uppercase tracking-[0.16em] text-stone-500">
                Carry
              </div>
              <div className="flex gap-2">
                {blocks.map((block) => (
                  <LinkedCell
                    key={`linked-carry-${block.index}`}
                    activeIndex={activeIndex}
                    index={block.index}
                    label={String(block.incoming)}
                    tone="carry"
                    onSelect={(index) => {
                      setIsPlaying(false);
                      setActiveIndex(index);
                    }}
                  />
                ))}
              </div>
            </div>

            <div className="flex items-center gap-3">
              <div className="w-24 shrink-0 text-xs font-bold uppercase tracking-[0.16em] text-stone-500">
                Visible
              </div>
              <div className="flex gap-2">
                {blocks.map((block) => (
                  <LinkedCell
                    key={`linked-visible-${block.index}`}
                    activeIndex={activeIndex}
                    index={block.index}
                    label={formatBlock(block.visible, PRIME97_BRIDGE_EXAMPLE.blockWidth)}
                    tone="visible"
                    onSelect={(index) => {
                      setIsPlaying(false);
                      setActiveIndex(index);
                    }}
                  />
                ))}
              </div>
            </div>

            <div className="flex items-center gap-3">
              <div className="w-24 shrink-0 text-xs font-bold uppercase tracking-[0.16em] text-stone-500">
                Actual
              </div>
              <div className="flex gap-2">
                {blocks.map((block) => (
                  <LinkedCell
                    key={`linked-actual-${block.index}`}
                    activeIndex={activeIndex}
                    index={block.index}
                    label={formatBlock(block.actual, PRIME97_BRIDGE_EXAMPLE.blockWidth)}
                    tone="actual"
                    onSelect={(index) => {
                      setIsPlaying(false);
                      setActiveIndex(index);
                    }}
                  />
                ))}
              </div>
            </div>
          </div>

          <div className="mt-4 rounded-2xl bg-stone-50 p-4 text-sm leading-relaxed text-stone-800">
            <div className="font-mono">{currentEquation}</div>
            <div className="mt-2 font-mono">{currentRemainderEquation}</div>
            <div className="mt-2 font-mono">{currentPhaseEquation}</div>
          </div>
        </article>
      </div>
    </div>
  );
};

export default LinkedViews97;
