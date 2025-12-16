import { useState, useMemo } from 'react';
import {
  findGoodCoordinates,
  skeletonBlocks,
  rawPowers,
  applyCarry,
  computeReptend,
  multiplicativeOrder,
  GoodCoordinateEntry
} from '../lib/math';

const PRESET_MODULI = [19, 37, 97, 199];
const PRESET_BASES = [2, 7, 10, 12];

// =============================================================================
// Quality Bar Component
// =============================================================================

interface QualityBarProps {
  k: number;
  M: number;
  isGood: boolean;
}

const QualityBar = ({ k, M, isGood }: QualityBarProps) => {
  // Quality = 1 - k/M (higher is better, max 1 when k=1)
  const quality = 1 - k / M;
  const widthPercent = Math.max(5, quality * 100);

  // Color based on k value
  const barColor = k === 1
    ? 'bg-emerald-500'
    : k <= 3
      ? 'bg-emerald-400'
      : k <= 5
        ? 'bg-amber-400'
        : 'bg-stone-300';

  return (
    <div className="flex items-center gap-1">
      <div className="w-16 h-2 bg-stone-200 rounded-full overflow-hidden">
        <div
          className={`h-full ${barColor} transition-all duration-300`}
          style={{ width: `${widthPercent}%` }}
        />
      </div>
      {isGood && (
        <span className="text-[10px] text-stone-500">
          {k === 1 ? '★' : ''}
        </span>
      )}
    </div>
  );
};

// =============================================================================
// K-Pattern Chart (Mini sparkline showing k values)
// =============================================================================

interface KPatternChartProps {
  entries: GoodCoordinateEntry[];
  M: number;
  orderOfBase: number;
}

const KPatternChart = ({ entries, M, orderOfBase }: KPatternChartProps) => {
  const maxK = Math.max(...entries.map(e => e.k));
  const height = 40;
  const barWidth = 100 / entries.length;

  return (
    <div className="bg-stone-100 rounded p-3 mb-4">
      <div className="flex justify-between items-center mb-2">
        <span className="text-xs text-stone-600">k values across block widths m=1..{entries.length}</span>
        <span className="text-xs text-stone-500 font-mono">
          ord<sub>{M}</sub>(base) = {orderOfBase}
        </span>
      </div>

      {/* Chart */}
      <div className="relative" style={{ height }}>
        <svg width="100%" height={height} className="overflow-visible">
          {/* Threshold line at k=5 */}
          <line
            x1="0"
            y1={height - (5 / maxK) * height}
            x2="100%"
            y2={height - (5 / maxK) * height}
            stroke="#a8a29e"
            strokeWidth="1"
            strokeDasharray="2,2"
          />

          {/* Bars */}
          {entries.map((entry, i) => {
            const barHeight = (entry.k / maxK) * height;
            const x = i * barWidth;
            const isGood = entry.k >= 1 && entry.k <= 5;
            const isPerfect = entry.k === 1;

            return (
              <g key={entry.m}>
                <rect
                  x={`${x + barWidth * 0.1}%`}
                  y={height - barHeight}
                  width={`${barWidth * 0.8}%`}
                  height={barHeight}
                  className={
                    isPerfect
                      ? 'fill-emerald-500'
                      : isGood
                        ? 'fill-emerald-300'
                        : 'fill-stone-300'
                  }
                  rx="1"
                />
                {/* m label for good coordinates */}
                {isGood && (
                  <text
                    x={`${x + barWidth * 0.5}%`}
                    y={height - barHeight - 3}
                    textAnchor="middle"
                    className="fill-stone-600 text-[8px] font-mono"
                  >
                    {entry.m}
                  </text>
                )}
              </g>
            );
          })}
        </svg>
      </div>

      {/* Periodicity note */}
      {orderOfBase < entries.length && (
        <div className="mt-2 text-xs text-stone-500 border-t border-stone-200 pt-2">
          <span className="text-emerald-600 font-medium">Pattern repeats every {orderOfBase} steps</span>
          {' '}— k values cycle because base<sup>{orderOfBase}</sup> ≡ 1 (mod {M})
        </div>
      )}
    </div>
  );
};

// =============================================================================
// Skeleton × q Visual
// =============================================================================

interface SkeletonMultiplyVisualProps {
  skeleton: string[];
  q: number;
  actual: string[];
  k: number;
  m: number;
}

const SkeletonMultiplyVisual = ({ skeleton, q, actual, k, m }: SkeletonMultiplyVisualProps) => {
  const showBlocks = 4;

  return (
    <div className="bg-gradient-to-r from-stone-100 to-emerald-50 rounded-lg p-4 border border-stone-200">
      <div className="flex flex-col sm:flex-row items-center justify-center gap-3 sm:gap-4">
        {/* Skeleton blocks */}
        <div className="text-center">
          <div className="text-[10px] text-stone-500 mb-1">Skeleton (k<sup>j</sup>)</div>
          <div className="flex gap-1 font-mono text-sm">
            {skeleton.slice(0, showBlocks).map((block, i) => (
              <span
                key={i}
                className={`px-2 py-1 rounded ${
                  block.startsWith('[')
                    ? 'bg-amber-100 text-amber-700'
                    : 'bg-stone-200 text-stone-700'
                }`}
              >
                {block}
              </span>
            ))}
            <span className="text-stone-400 self-center">...</span>
          </div>
        </div>

        {/* Multiply symbol */}
        <div className="flex flex-col items-center">
          <span className="text-2xl text-stone-400">×</span>
          <span className="font-mono text-lg font-bold text-violet-600">{q}</span>
        </div>

        {/* Equals */}
        <span className="text-2xl text-stone-400">=</span>

        {/* Actual blocks */}
        <div className="text-center">
          <div className="text-[10px] text-stone-500 mb-1">Actual reptend</div>
          <div className="flex gap-1 font-mono text-sm">
            {actual.slice(0, showBlocks).map((block, i) => (
              <span
                key={i}
                className="px-2 py-1 rounded bg-emerald-200 text-emerald-800 font-semibold"
              >
                {block}
              </span>
            ))}
            <span className="text-stone-400 self-center">...</span>
          </div>
        </div>
      </div>

      {/* Special message for k=1 */}
      {k === 1 && (
        <div className="mt-3 text-center text-sm text-emerald-700 font-medium">
          When k=1, skeleton is all <span className="font-mono">{"1".padStart(m, '0')}</span>s,
          so each reptend block = q = <span className="font-mono">{q}</span>
        </div>
      )}
    </div>
  );
};

// =============================================================================
// Perfect Coordinate Celebration
// =============================================================================

interface PerfectCelebrationProps {
  M: number;
  m: number;
  q: number;
  B: number;
}

const PerfectCelebration = ({ M, m, q, B }: PerfectCelebrationProps) => (
  <div className="bg-gradient-to-br from-emerald-100 via-emerald-50 to-amber-50 border-2 border-emerald-300 rounded-xl p-4 sm:p-6 text-center">
    <div className="text-3xl mb-2">✨</div>
    <h4 className="text-lg font-serif font-bold text-emerald-800 mb-2">
      Perfect Coordinate!
    </h4>
    <div className="font-mono text-sm text-emerald-700 space-y-1">
      <div>{B.toLocaleString()} = {q.toLocaleString()} × {M} + <span className="text-2xl font-bold">1</span></div>
      <div className="text-stone-600 mt-2">
        The reptend of 1/{M} is simply <span className="text-emerald-700 font-bold">{q.toString().padStart(m, '0')}</span> repeating
      </div>
    </div>
    <div className="mt-3 text-xs text-stone-500">
      k=1 means the geometric skeleton is constant — no growth, no overflow, pure structure
    </div>
  </div>
);

// =============================================================================
// Detail Panel
// =============================================================================

interface DetailPanelProps {
  M: number;
  base: number;
  entry: GoodCoordinateEntry;
  onClose: () => void;
}

const DetailPanel = ({ M, base, entry, onClose }: DetailPanelProps) => {
  const { m, B, k, q } = entry;
  const blockCount = 8;

  // Get skeleton (raw powers of k)
  const skeleton = skeletonBlocks(k, m, blockCount);

  // Get skeleton with carry applied
  const raw = rawPowers(k, blockCount);
  const withCarry = applyCarry(raw, B, m);

  // Get actual reptend blocks from long division
  // Note: computeReptend is base-10 only for now
  const reptend = base === 10 ? computeReptend(M) : '';
  const actualBlocks: string[] = [];
  if (reptend) {
    for (let i = 0; i < blockCount && i * m < reptend.length; i++) {
      actualBlocks.push(reptend.slice(i * m, (i + 1) * m).padEnd(m, '0'));
    }
  }

  const isPerfect = k === 1;

  return (
    <div className="fixed inset-0 bg-black/50 flex items-center justify-center p-4 z-50">
      <div className="bg-stone-100 rounded-lg shadow-xl max-w-2xl w-full p-4 sm:p-6 max-h-[90vh] overflow-y-auto">
        <div className="flex justify-between items-start mb-4">
          <h3 className="text-base sm:text-lg font-serif font-medium text-stone-900">
            {isPerfect ? '✨ ' : ''}Good Coordinate: M={M}, m={m}, base={base}
          </h3>
          <button
            onClick={onClose}
            className="text-stone-400 hover:text-stone-600 text-xl leading-none min-h-[44px] min-w-[44px] flex items-center justify-center -mr-2 -mt-2"
          >
            ×
          </button>
        </div>

        <div className="space-y-4 text-stone-700 text-sm sm:text-base">
          {/* Perfect celebration or standard decomposition */}
          {isPerfect ? (
            <PerfectCelebration M={M} m={m} q={q} B={B} />
          ) : (
            <div className="bg-stone-200 rounded px-3 sm:px-4 py-3 font-mono text-xs sm:text-sm space-y-1">
              <div className="text-stone-600 mb-2">Canonical Decomposition:</div>
              <div className="text-stone-900 font-semibold">
                {B.toLocaleString()} = {q.toLocaleString()} × {M} + {k}
              </div>
              <div className="text-stone-600 mt-2">Identity:</div>
              <div className="text-stone-900">
                1/{M} = {q}/{B - k} = {q}/({B}-{k})
              </div>
            </div>
          )}

          {/* Visual: skeleton × q = actual */}
          {actualBlocks.length > 0 && (
            <SkeletonMultiplyVisual
              skeleton={skeleton}
              q={q}
              actual={actualBlocks}
              k={k}
              m={m}
            />
          )}

          {/* Detailed breakdown for k > 1 */}
          {k > 1 && (
            <>
              {/* Skeleton blocks */}
              <div>
                <div className="font-medium mb-2">
                  Skeleton (k<sup>j</sup> = {k}<sup>j</sup>):
                </div>
                <div className="bg-stone-200 rounded px-3 py-2 font-mono text-xs sm:text-sm overflow-x-auto">
                  <div className="flex gap-2 flex-wrap">
                    {skeleton.map((block, i) => (
                      <span
                        key={i}
                        className={block.startsWith('[') ? 'text-amber-600' : 'text-stone-800'}
                      >
                        {block}
                      </span>
                    ))}
                    <span className="text-stone-400">...</span>
                  </div>
                </div>
              </div>

              {/* With carry */}
              <div>
                <div className="font-medium mb-2">After carry propagation:</div>
                <div className="bg-stone-200 rounded px-3 py-2 font-mono text-xs sm:text-sm overflow-x-auto">
                  <div className="flex gap-2 flex-wrap">
                    {withCarry.map((block, i) => (
                      <span key={i} className="text-stone-800">{block}</span>
                    ))}
                    <span className="text-stone-400">...</span>
                  </div>
                </div>
              </div>
            </>
          )}

          {/* Full reptend for reference */}
          {reptend && (
            <div>
              <div className="text-xs text-stone-500 mb-1">Full reptend ({reptend.length} digits):</div>
              <div className="font-mono text-xs bg-stone-200 rounded px-3 py-2 break-all max-h-20 overflow-y-auto">
                0.{reptend}...
              </div>
            </div>
          )}
        </div>
      </div>
    </div>
  );
};

// =============================================================================
// Coordinates Table
// =============================================================================

interface CoordinatesTableProps {
  M: number;
  base: number;
  entries: GoodCoordinateEntry[];
  onRowClick: (entry: GoodCoordinateEntry) => void;
}

const CoordinatesTable = ({ M, base, entries, onRowClick }: CoordinatesTableProps) => (
  <div className="overflow-x-auto -mx-4 sm:mx-0">
    <table className="w-full text-xs sm:text-sm border-collapse bg-stone-50 rounded min-w-[600px]">
      <thead>
        <tr className="border-b border-stone-300 bg-stone-200">
          <th className="py-2 px-2 sm:px-3 text-left font-medium text-stone-600">m</th>
          <th className="py-2 px-2 sm:px-3 text-left font-medium text-stone-600">B = {base}<sup>m</sup></th>
          <th className="py-2 px-2 sm:px-3 text-left font-medium text-stone-600">k = B mod {M}</th>
          <th className="py-2 px-2 sm:px-3 text-left font-medium text-stone-600">q = (B-k)/{M}</th>
          <th className="py-2 px-2 sm:px-3 text-center font-medium text-stone-600">Quality</th>
          <th className="py-2 px-2 sm:px-3 text-left font-medium text-stone-600">Identity</th>
        </tr>
      </thead>
      <tbody className="font-mono text-stone-700">
        {entries.map((entry) => {
          const isClickable = entry.isGood;

          return (
            <tr
              key={entry.m}
              onClick={() => isClickable && onRowClick(entry)}
              className={`border-b border-stone-200 transition-colors ${
                entry.isGood
                  ? entry.k === 1
                    ? 'bg-emerald-100 hover:bg-emerald-200 cursor-pointer'
                    : 'bg-emerald-50 hover:bg-emerald-100 cursor-pointer'
                  : 'hover:bg-stone-100'
              }`}
            >
              <td className="py-2 px-2 sm:px-3">{entry.m}</td>
              <td className="py-2 px-2 sm:px-3">{entry.B.toLocaleString()}</td>
              <td className={`py-2 px-2 sm:px-3 ${
                entry.k === 1
                  ? 'text-emerald-700 font-bold'
                  : entry.isGood
                    ? 'text-emerald-600 font-semibold'
                    : ''
              }`}>
                {entry.k}
                {entry.k === 1 && ' ✨'}
              </td>
              <td className="py-2 px-2 sm:px-3">{entry.q.toLocaleString()}</td>
              <td className="py-2 px-2 sm:px-3">
                <QualityBar k={entry.k} M={M} isGood={entry.isGood} />
              </td>
              <td className="py-2 px-2 sm:px-3 text-stone-500">
                {entry.isGood && (
                  <span>
                    1/{M} = {entry.q}/{entry.B - entry.k}
                  </span>
                )}
              </td>
            </tr>
          );
        })}
      </tbody>
    </table>
  </div>
);

// =============================================================================
// Main Component
// =============================================================================

const GoodCoordinatesExplorer = () => {
  const [M, setM] = useState(37);
  const [customM, setCustomM] = useState('');
  const [base, setBase] = useState(10);
  const [customBase, setCustomBase] = useState('');
  const [maxM] = useState(12);
  const [kThreshold] = useState(5);
  const [selectedEntry, setSelectedEntry] = useState<GoodCoordinateEntry | null>(null);

  const entries = useMemo(
    () => findGoodCoordinates(M, base, maxM, kThreshold),
    [M, base, maxM, kThreshold]
  );

  const orderOfBase = useMemo(
    () => multiplicativeOrder(base, M),
    [base, M]
  );

  const goodCount = entries.filter(e => e.isGood).length;
  const bestEntry = entries.reduce((best, e) =>
    e.isGood && (!best || e.k < best.k) ? e : best,
    null as GoodCoordinateEntry | null
  );

  const handleCustomM = () => {
    const val = parseInt(customM, 10);
    // Check coprime to base
    if (val > 1) {
      const gcd = (a: number, b: number): number => b === 0 ? a : gcd(b, a % b);
      if (gcd(val, base) === 1) {
        setM(val);
        setCustomM('');
      }
    }
  };

  const handleCustomBase = () => {
    const val = parseInt(customBase, 10);
    if (val >= 2) {
      const gcd = (a: number, b: number): number => b === 0 ? a : gcd(b, a % b);
      if (gcd(M, val) === 1) {
        setBase(val);
        setCustomBase('');
      }
    }
  };

  return (
    <section className="mb-8 sm:mb-10">
      <h2 className="text-lg sm:text-xl font-serif font-bold text-stone-900 mb-3 sm:mb-4">
        Good Coordinates Explorer
      </h2>

      <p className="text-stone-700 leading-relaxed mb-4 text-sm sm:text-base">
        Every modulus M has a <strong>canonical decomposition</strong> at each block width m:{' '}
        <span className="font-mono bg-stone-200 px-1 rounded">B = qM + k</span> where B = base<sup>m</sup>.
        When k is small, the geometric skeleton is visible—we call this a{' '}
        <em className="text-emerald-700">good coordinate</em>.
      </p>

      {/* Selectors Row */}
      <div className="flex flex-col sm:flex-row gap-4 mb-4">
        {/* Modulus selector */}
        <div className="flex flex-wrap gap-2 items-center">
          <span className="text-stone-600 text-sm font-medium">M =</span>
          {PRESET_MODULI.map((preset) => (
            <button
              key={preset}
              onClick={() => setM(preset)}
              className={`px-3 py-2 min-h-[44px] rounded font-mono text-xs sm:text-sm transition-colors ${
                preset === M
                  ? 'bg-stone-800 text-stone-100'
                  : 'bg-stone-200 text-stone-700 hover:bg-stone-300'
              }`}
            >
              {preset}
            </button>
          ))}
          <div className="flex gap-1">
            <input
              type="number"
              value={customM}
              onChange={(e) => setCustomM(e.target.value)}
              onKeyDown={(e) => e.key === 'Enter' && handleCustomM()}
              placeholder="custom"
              className="w-20 px-2 py-2 min-h-[44px] rounded border border-stone-300 font-mono text-xs sm:text-sm"
            />
            <button
              onClick={handleCustomM}
              className="px-3 py-2 min-h-[44px] rounded bg-stone-200 text-stone-700 hover:bg-stone-300 text-xs sm:text-sm"
            >
              Go
            </button>
          </div>
        </div>

        {/* Base selector */}
        <div className="flex flex-wrap gap-2 items-center">
          <span className="text-stone-600 text-sm font-medium">base =</span>
          {PRESET_BASES.map((b) => (
            <button
              key={b}
              onClick={() => setBase(b)}
              className={`px-3 py-2 min-h-[44px] rounded font-mono text-xs sm:text-sm transition-colors ${
                b === base
                  ? 'bg-violet-700 text-white'
                  : 'bg-violet-100 text-violet-700 hover:bg-violet-200'
              }`}
            >
              {b}
            </button>
          ))}
          <div className="flex gap-1">
            <input
              type="number"
              value={customBase}
              onChange={(e) => setCustomBase(e.target.value)}
              onKeyDown={(e) => e.key === 'Enter' && handleCustomBase()}
              placeholder="other"
              className="w-16 px-2 py-2 min-h-[44px] rounded border border-violet-300 font-mono text-xs sm:text-sm"
            />
            <button
              onClick={handleCustomBase}
              className="px-3 py-2 min-h-[44px] rounded bg-violet-100 text-violet-700 hover:bg-violet-200 text-xs sm:text-sm"
            >
              Go
            </button>
          </div>
        </div>
      </div>

      {/* Key equation display */}
      <div className="bg-stone-200 rounded px-3 sm:px-4 py-3 mb-4 font-mono text-xs sm:text-sm">
        <div className="text-stone-600 mb-1">The Canonical Decomposition:</div>
        <div className="text-stone-800 flex flex-col sm:flex-row sm:items-center gap-1 sm:gap-4">
          <span className="font-semibold">B = qM + k</span>
          <span className="text-stone-500">⇒</span>
          <span>1/M = q/(B-k)</span>
        </div>
        {bestEntry && (
          <div className="mt-2 pt-2 border-t border-stone-300 text-emerald-700">
            Best for M={M} in base {base}: m={bestEntry.m} gives k={bestEntry.k}
            {bestEntry.k === 1 && ' ✨ (perfect!)'}
          </div>
        )}
      </div>

      {/* K-Pattern Chart */}
      <KPatternChart
        entries={entries}
        M={M}
        orderOfBase={orderOfBase}
      />

      {/* Summary */}
      <div className="text-sm text-stone-600 mb-3">
        Found <span className="font-semibold text-emerald-700">{goodCount}</span> good coordinate{goodCount !== 1 ? 's' : ''}{' '}
        (k ≤ {kThreshold}) in m = 1..{maxM}.
        {goodCount > 0 && <span className="text-stone-500"> Click a highlighted row for details.</span>}
      </div>

      {/* Table */}
      <CoordinatesTable
        M={M}
        base={base}
        entries={entries}
        onRowClick={setSelectedEntry}
      />

      {/* Legend */}
      <div className="mt-3 text-[10px] sm:text-xs text-stone-500 flex flex-wrap gap-4">
        <span>Quality bar shows 1 - k/M (higher = better)</span>
        <span>✨ = perfect (k=1)</span>
      </div>

      {/* Link to k-family explorer */}
      {bestEntry && bestEntry.k <= 11 && (
        <div className="mt-4 p-3 bg-violet-50 border border-violet-200 rounded text-sm">
          <span className="text-violet-700">
            <strong>Dual view:</strong> This explorer fixes M and varies m.
            The k-Family Explorer below fixes k={bestEntry.k} and finds all primes where {base}<sup>m</sup> ≡ {bestEntry.k} (mod p).
          </span>
        </div>
      )}

      {/* Detail modal */}
      {selectedEntry && (
        <DetailPanel
          M={M}
          base={base}
          entry={selectedEntry}
          onClose={() => setSelectedEntry(null)}
        />
      )}
    </section>
  );
};

export default GoodCoordinatesExplorer;
