import { useMemo, useState } from 'react';
import { isPrime, multiplicativeOrder } from '../lib/math';

interface SweepEntry {
  prime: number;
  blockBase: number;
  quotient: number;
  remainderK: number;
  blockPeriod: number;
  digitPeriod: number;
  firstIncomingCarry: number | null;
  visibleBlocks: string[];
  carryProfile: number[];
  regime: 'no-carry' | 'late-carry' | 'early-carry';
  subgroupType: 'qr-full' | 'degenerate';
}

const BLOCK_BASE = 100;
const BLOCK_WIDTH = 2;

function formatBlock(value: number): string {
  return value.toString().padStart(BLOCK_WIDTH, '0');
}

function buildSweep(): SweepEntry[] {
  const out: SweepEntry[] = [];

  for (let prime = 3; prime < 100; prime += 2) {
    if (!isPrime(prime) || prime === 5) {
      continue;
    }

    const remainderK = BLOCK_BASE % prime;
    const quotient = (BLOCK_BASE - remainderK) / prime;
    const blockPeriod = multiplicativeOrder(BLOCK_BASE % prime, prime);
    const digitPeriod = multiplicativeOrder(10, prime);

    let firstIncomingCarry: number | null = null;
    if (remainderK !== 1) {
      const threshold = BLOCK_BASE - remainderK;
      for (let index = 0; index < 16; index++) {
        if (quotient * remainderK ** (index + 1) >= threshold) {
          firstIncomingCarry = index;
          break;
        }
      }
    }

    const visibleBlocks: string[] = [];
    const carryProfile: number[] = [];
    let remainder = 1;
    for (let index = 0; index < Math.min(blockPeriod, 9); index++) {
      const digit = Math.floor((BLOCK_BASE * remainder) / prime);
      visibleBlocks.push(formatBlock(digit));
      carryProfile.push(
        Math.floor((quotient * remainderK ** (index + 1)) / (BLOCK_BASE - remainderK)),
      );
      remainder = (BLOCK_BASE * remainder) % prime;
    }

    out.push({
      prime,
      blockBase: BLOCK_BASE,
      quotient,
      remainderK,
      blockPeriod,
      digitPeriod,
      firstIncomingCarry,
      visibleBlocks,
      carryProfile,
      regime:
        firstIncomingCarry == null
          ? 'no-carry'
          : firstIncomingCarry >= 3
          ? 'late-carry'
          : 'early-carry',
      subgroupType: blockPeriod === (prime - 1) / 2 ? 'qr-full' : 'degenerate',
    });
  }

  return out;
}

function pointForEntry(
  entry: SweepEntry,
  maxCarryBand: number,
): { x: number; y: number } {
  const x = 58 + ((entry.remainderK - 1) / 96) * 420;
  const carryBand = entry.firstIncomingCarry == null ? maxCarryBand : entry.firstIncomingCarry;
  const y = 48 + (1 - carryBand / maxCarryBand) * 220;
  return { x, y };
}

const regimeStyles: Record<SweepEntry['regime'], string> = {
  'no-carry': 'bg-stone-100 text-stone-700',
  'late-carry': 'bg-emerald-100 text-emerald-900',
  'early-carry': 'bg-amber-100 text-amber-900',
};

const PrimeFamilySweep100 = () => {
  const entries = useMemo(() => buildSweep(), []);
  const [selectedPrime, setSelectedPrime] = useState(97);

  const selected =
    entries.find((entry) => entry.prime === selectedPrime) ?? entries[entries.length - 1];
  const maxBlockPeriod = Math.max(...entries.map((entry) => entry.blockPeriod));
  const maxCarryBand = Math.max(
    ...entries.map((entry) => (entry.firstIncomingCarry == null ? 5 : entry.firstIncomingCarry)),
  );
  const outliers = entries.filter(
    (entry) =>
      entry.firstIncomingCarry == null ||
      entry.firstIncomingCarry >= 2 ||
      entry.prime === 19 ||
      entry.prime === 97,
  );

  return (
    <div className="mb-6 rounded-[1.85rem] border border-stone-200 bg-linear-to-br from-white via-stone-50 to-lime-50/45 p-5 shadow-sm sm:p-6">
      <div className="max-w-3xl">
        <div className="text-xs font-bold uppercase tracking-[0.22em] text-stone-500">
          Family Sweep
        </div>
        <h3 className="mt-2 text-xl font-serif font-semibold tracking-tight text-stone-900 sm:text-2xl">
          Prime landscape in the shared B = 100 coordinate
        </h3>
        <p className="mt-3 text-sm leading-relaxed text-stone-700 sm:text-base">
          This sweep fixes the same block coordinate for every prime <code>p &lt; 100</code> coprime to
          <code>10</code>: <code>B = 100 = q p + k</code>. The scatter plots
          <code> k </code> against the first incoming-carry position. Dot size reflects block period
          <code> ord_p(100) </code>, and the detail pane lets us inspect a selected prime’s local shape.
        </p>
      </div>

      <div className="mt-6 grid gap-6 xl:grid-cols-[1.15fr_0.85fr]">
        <article className="rounded-[1.5rem] border border-stone-200 bg-white/90 p-4">
          <div className="flex flex-wrap items-center justify-between gap-3">
            <div>
              <div className="text-xs font-bold uppercase tracking-[0.18em] text-stone-500">
                Sweep Map
              </div>
              <div className="mt-1 text-sm font-semibold text-stone-900">
                x = remainder k, y = first incoming carry
              </div>
            </div>
            <div className="rounded-full bg-lime-100 px-3 py-1 text-xs font-bold uppercase tracking-wide text-lime-900">
              23 primes under 100
            </div>
          </div>

          <div className="mt-4 rounded-2xl border border-stone-200 bg-stone-50 p-3">
            <svg viewBox="0 0 540 310" className="w-full">
              <line x1="52" y1="270" x2="500" y2="270" stroke="#a8a29e" strokeWidth="1.5" />
              <line x1="52" y1="34" x2="52" y2="270" stroke="#a8a29e" strokeWidth="1.5" />

              {[1, 5, 10, 20, 40, 60, 80, 97].map((tick) => {
                const x = 58 + ((tick - 1) / 96) * 420;
                return (
                  <g key={`x-${tick}`}>
                    <line x1={x} y1="266" x2={x} y2="274" stroke="#a8a29e" strokeWidth="1" />
                    <text x={x} y="290" textAnchor="middle" className="fill-stone-400 text-[10px] font-mono">
                      {tick}
                    </text>
                  </g>
                );
              })}

              {Array.from({ length: maxCarryBand + 1 }, (_, index) => index).map((band) => {
                const y = 48 + (1 - band / maxCarryBand) * 220;
                return (
                  <g key={`y-${band}`}>
                    <line x1="48" y1={y} x2="56" y2={y} stroke="#a8a29e" strokeWidth="1" />
                    <text x="38" y={y + 3} textAnchor="end" className="fill-stone-400 text-[10px] font-mono">
                      {band === maxCarryBand ? 'none' : band}
                    </text>
                  </g>
                );
              })}

              <text x="280" y="304" textAnchor="middle" className="fill-stone-500 text-[11px] font-semibold uppercase tracking-[0.16em]">
                remainder k = 100 mod p
              </text>
              <text
                x="14"
                y="158"
                textAnchor="middle"
                transform="rotate(-90 14 158)"
                className="fill-stone-500 text-[11px] font-semibold uppercase tracking-[0.16em]"
              >
                first incoming carry
              </text>

              {entries.map((entry) => {
                const point = pointForEntry(entry, maxCarryBand);
                const isSelected = entry.prime === selected.prime;
                const radius = 5 + (entry.blockPeriod / maxBlockPeriod) * 7;
                const fill =
                  entry.regime === 'no-carry'
                    ? '#d6d3d1'
                    : entry.regime === 'late-carry'
                    ? '#34d399'
                    : '#f59e0b';
                const stroke = entry.subgroupType === 'qr-full' ? '#0f172a' : '#7c3aed';

                return (
                  <g key={`prime-${entry.prime}`}>
                    <circle
                      cx={point.x}
                      cy={point.y}
                      r={isSelected ? radius + 2 : radius}
                      fill={fill}
                      stroke={stroke}
                      strokeWidth={isSelected ? 2.8 : 1.5}
                      onClick={() => setSelectedPrime(entry.prime)}
                      className="cursor-pointer"
                    />
                    {(entry.prime === 19 || entry.prime === 97 || entry.firstIncomingCarry == null) ? (
                      <text
                        x={point.x}
                        y={point.y - radius - 6}
                        textAnchor="middle"
                        className={`text-[10px] font-mono font-semibold ${
                          isSelected ? 'fill-stone-900' : 'fill-stone-500'
                        }`}
                      >
                        {entry.prime}
                      </text>
                    ) : null}
                  </g>
                );
              })}
            </svg>
          </div>

          <div className="mt-4 grid gap-3 sm:grid-cols-3 text-sm leading-relaxed text-stone-700">
            <div className="rounded-2xl bg-stone-50 p-3">
              <div className="font-semibold text-stone-900">Big cluster</div>
              <div className="mt-2">
                Most primes land at <code>j = 1</code>: the geometry may be clean, but the carry layer
                starts shaping visible blocks almost immediately.
              </div>
            </div>
            <div className="rounded-2xl bg-stone-50 p-3">
              <div className="font-semibold text-stone-900">Rare delay</div>
              <div className="mt-2">
                Only a few primes reach <code>j ≥ 2</code>, and <code>97</code> is the standout at
                <code>j = 4</code>.
              </div>
            </div>
            <div className="rounded-2xl bg-stone-50 p-3">
              <div className="font-semibold text-stone-900">Constant skeleton</div>
              <div className="mt-2">
                <code>p = 3</code> and <code>p = 11</code> sit at <code>k = 1</code>, so their
                carry boundary never arrives in this coordinate.
              </div>
            </div>
          </div>
        </article>

        <aside className="space-y-4">
          <div className="rounded-[1.5rem] border border-stone-200 bg-white/90 p-4">
            <div className="flex flex-wrap items-center justify-between gap-3">
              <div>
                <div className="text-xs font-bold uppercase tracking-[0.18em] text-stone-500">
                  Selected Prime
                </div>
                <div className="mt-1 text-lg font-serif font-semibold text-stone-900">
                  1/{selected.prime}
                </div>
              </div>
              <div className={`rounded-full px-3 py-1 text-xs font-bold uppercase tracking-wide ${regimeStyles[selected.regime]}`}>
                {selected.firstIncomingCarry == null
                  ? 'no incoming carry'
                  : `carry at j=${selected.firstIncomingCarry}`}
              </div>
            </div>

            <div className="mt-4 grid gap-3 sm:grid-cols-2">
              <div className="rounded-2xl bg-stone-50 p-3">
                <div className="text-xs font-bold uppercase tracking-[0.16em] text-stone-500">
                  Coordinate
                </div>
                <div className="mt-2 font-mono text-sm text-stone-900">
                  100 = {selected.quotient}×{selected.prime} + {selected.remainderK}
                </div>
              </div>
              <div className="rounded-2xl bg-stone-50 p-3">
                <div className="text-xs font-bold uppercase tracking-[0.16em] text-stone-500">
                  Periods
                </div>
                <div className="mt-2 font-mono text-sm text-stone-900">
                  blocks: {selected.blockPeriod}
                </div>
                <div className="mt-1 font-mono text-sm text-stone-900">
                  digits: {selected.digitPeriod}
                </div>
              </div>
              <div className="rounded-2xl bg-stone-50 p-3">
                <div className="text-xs font-bold uppercase tracking-[0.16em] text-stone-500">
                  Subgroup type
                </div>
                <div className="mt-2 font-mono text-sm text-stone-900">
                  {selected.subgroupType === 'qr-full' ? 'full QR subgroup' : 'proper divisor of QR'}
                </div>
              </div>
              <div className="rounded-2xl bg-stone-50 p-3">
                <div className="text-xs font-bold uppercase tracking-[0.16em] text-stone-500">
                  First carry
                </div>
                <div className="mt-2 font-mono text-sm text-stone-900">
                  {selected.firstIncomingCarry == null ? 'none' : `j = ${selected.firstIncomingCarry}`}
                </div>
              </div>
            </div>

            <div className="mt-4 rounded-2xl border border-stone-200 bg-stone-50 p-3">
              <div className="text-xs font-bold uppercase tracking-[0.16em] text-stone-500">
                Visible block prefix
              </div>
              <div className="mt-3 flex flex-wrap gap-2">
                {selected.visibleBlocks.map((block, index) => {
                  const carryActive =
                    selected.firstIncomingCarry != null && index >= selected.firstIncomingCarry;
                  return (
                    <div
                      key={`selected-${selected.prime}-${index}`}
                      className={`rounded-xl border px-3 py-2 font-mono text-sm ${
                        carryActive
                          ? 'border-amber-200 bg-amber-50 text-amber-900'
                          : 'border-emerald-200 bg-emerald-50 text-emerald-900'
                      }`}
                    >
                      <div className="text-[10px] uppercase tracking-[0.16em] opacity-60">j={index}</div>
                      <div className="mt-1 font-semibold">{block}</div>
                    </div>
                  );
                })}
              </div>
            </div>

            <div className="mt-4 rounded-2xl border border-stone-200 bg-stone-50 p-3">
              <div className="text-xs font-bold uppercase tracking-[0.16em] text-stone-500">
                Incoming carry profile
              </div>
              <div className="mt-3 flex flex-wrap gap-2">
                {selected.carryProfile.map((carry, index) => (
                  <div
                    key={`carry-profile-${selected.prime}-${index}`}
                    className={`rounded-xl border px-3 py-2 font-mono text-sm ${
                      carry > 0
                        ? 'border-orange-200 bg-orange-50 text-orange-900'
                        : 'border-stone-200 bg-white text-stone-700'
                    }`}
                  >
                    <div className="text-[10px] uppercase tracking-[0.16em] opacity-60">c_{index}</div>
                    <div className="mt-1 font-semibold">{carry}</div>
                  </div>
                ))}
              </div>
            </div>
          </div>

          <div className="rounded-[1.5rem] border border-stone-200 bg-white/90 p-4">
            <div className="text-xs font-bold uppercase tracking-[0.18em] text-stone-500">
              Notable Points
            </div>
            <div className="mt-3 flex flex-wrap gap-2">
              {outliers.map((entry) => (
                <button
                  key={`outlier-${entry.prime}`}
                  type="button"
                  onClick={() => setSelectedPrime(entry.prime)}
                  className={`rounded-full border px-3 py-1.5 text-sm font-semibold transition-colors ${
                    selected.prime === entry.prime
                      ? 'border-stone-900 bg-stone-900 text-stone-50'
                      : 'border-stone-300 bg-white text-stone-700 hover:bg-stone-100'
                  }`}
                >
                  p={entry.prime}
                </button>
              ))}
            </div>
            <div className="mt-4 text-sm leading-relaxed text-stone-700">
              This is already a useful design-space map for the shared coordinate: small
              <code> k </code> helps, but delayed carry is genuinely rare. That makes
              <code> 1/97 </code> special without making it look magically unique.
            </div>
          </div>
        </aside>
      </div>
    </div>
  );
};

export default PrimeFamilySweep100;
