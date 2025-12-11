import { useState } from 'react';

interface CaseData {
  k: number;
  n: number;
  label: string;
  terms: number;
  S: bigint;
  R: bigint;
  F: bigint;
  description: string;
}

/**
 * Tab-based comparison showing why driver choice matters.
 * Contrasts a "good" driver (sparse stacking) with a "bad" driver (collision).
 */
const FluxContrast = () => {
  const [activeTab, setActiveTab] = useState<'good' | 'bad'>('good');

  const goodCase: CaseData = {
    k: 5,
    n: 2,
    label: 'k = 5, n = 2 (stride-2)',
    terms: 9,
    S: 52631578947265625n,
    R: 52631578947368421n,
    F: 102796n,
    description: 'Terms spread across different positions. Minimal collision.',
  };

  const badCase: CaseData = {
    k: 10,
    n: 1,
    label: 'k = 10, n = 1 (natural)',
    terms: 18,
    S: 1111111111111111110n,
    R: 52631578947368421n,
    F: -1058479532163742689n,
    description: 'All terms pile into overlapping columns. Massive carries.',
  };

  const current = activeTab === 'good' ? goodCase : badCase;

  const formatBigInt = (n: bigint): string => {
    const str = n.toString();
    // Add commas for readability
    return str.replace(/\B(?=(\d{3})+(?!\d))/g, ',');
  };

  return (
    <div className="my-8 sm:my-10 bg-white border border-stone-200 rounded-xl shadow-lg overflow-hidden">
      {/* Header */}
      <div className="bg-gradient-to-r from-stone-700 to-stone-600 px-4 sm:px-5 py-3">
        <span className="text-[10px] sm:text-xs font-mono text-stone-400 uppercase tracking-wider">
          Comparison
        </span>
        <h3 className="text-stone-100 font-semibold text-sm">
          Driver Choice Matters: Flux as Representation Cost
        </h3>
      </div>

      {/* Tabs */}
      <div className="flex border-b border-stone-200">
        <button
          onClick={() => setActiveTab('good')}
          className={`flex-1 px-3 sm:px-4 py-2.5 sm:py-3 text-xs sm:text-sm font-mono transition-colors ${
            activeTab === 'good'
              ? 'bg-emerald-50 text-emerald-700 border-b-2 border-emerald-500'
              : 'bg-stone-50 text-stone-500 hover:bg-stone-100'
          }`}
        >
          ✓ Good: k=5, n=2
        </button>
        <button
          onClick={() => setActiveTab('bad')}
          className={`flex-1 px-3 sm:px-4 py-2.5 sm:py-3 text-xs sm:text-sm font-mono transition-colors ${
            activeTab === 'bad'
              ? 'bg-red-50 text-red-700 border-b-2 border-red-500'
              : 'bg-stone-50 text-stone-500 hover:bg-stone-100'
          }`}
        >
          ✗ Bad: k=10, n=1
        </button>
      </div>

      <div className="p-4 sm:p-5">
        {/* Visual: term distribution */}
        <div className="mb-6">
          <div className="text-[10px] sm:text-xs font-mono text-stone-500 uppercase tracking-wide mb-3">
            Where terms land in the 18-digit window
          </div>

          <div className="h-20 sm:h-24 bg-stone-100 rounded-lg relative overflow-hidden border border-stone-200">
            {activeTab === 'good' ? (
              <div className="absolute inset-0 flex items-end justify-around px-2 pb-2">
                {Array.from({ length: 9 }, (_, i) => (
                  <div
                    key={i}
                    className="w-4 sm:w-6 bg-emerald-500 rounded-t transition-all duration-300"
                    style={{ height: `${30 + (9 - i) * 7}%` }}
                  />
                ))}
              </div>
            ) : (
              <div className="absolute inset-0 flex items-end justify-end pr-4 pb-2">
                <div className="relative w-12 sm:w-16">
                  {Array.from({ length: 18 }, (_, i) => (
                    <div
                      key={i}
                      className="absolute bottom-0 right-0 bg-red-500 rounded-t opacity-60"
                      style={{
                        height: `${20 + i * 4}%`,
                        width: `${100 - i * 3}%`,
                        right: `${i * 2}px`,
                      }}
                    />
                  ))}
                </div>
                <div className="absolute left-4 top-1/2 -translate-y-1/2 text-red-600 text-[10px] sm:text-xs font-mono">
                  ← 18 terms piling up →
                </div>
              </div>
            )}
          </div>

          <p className="text-[10px] sm:text-xs text-stone-500 mt-2 text-center">
            {current.description}
          </p>
        </div>

        {/* Stats grid */}
        <div className="space-y-2 sm:space-y-3 font-mono text-xs sm:text-sm">
          <div className="flex justify-between items-center py-2 border-b border-stone-100">
            <span className="text-stone-500">Stack sum S</span>
            <span className="text-stone-700 text-[10px] sm:text-xs overflow-hidden text-ellipsis max-w-[140px] sm:max-w-[200px]">
              {formatBigInt(current.S)}
            </span>
          </div>
          <div className="flex justify-between items-center py-2 border-b border-stone-100">
            <span className="text-stone-500">Reptend R</span>
            <span className="text-stone-700 text-[10px] sm:text-xs">
              {formatBigInt(current.R)}
            </span>
          </div>
          <div
            className={`flex justify-between items-center py-2 rounded px-2 -mx-2 ${
              activeTab === 'good' ? 'bg-emerald-50' : 'bg-red-50'
            }`}
          >
            <span
              className={
                activeTab === 'good'
                  ? 'text-emerald-700 font-medium'
                  : 'text-red-700 font-medium'
              }
            >
              Flux F = R − S
            </span>
            <span
              className={`font-bold text-[10px] sm:text-xs ${
                activeTab === 'good' ? 'text-emerald-700' : 'text-red-700'
              }`}
            >
              {current.F > 0 ? '+' : ''}
              {formatBigInt(current.F)}
            </span>
          </div>
          <div className="flex justify-between items-center py-2">
            <span className="text-stone-500">|F/R| ratio</span>
            <span
              className={`font-bold ${
                activeTab === 'good' ? 'text-emerald-600' : 'text-red-600'
              }`}
            >
              {activeTab === 'good' ? '0.000002' : '20.1'}
              <span className="text-stone-400 font-normal ml-2">
                ({activeTab === 'good' ? 'tiny' : 'huge!'})
              </span>
            </span>
          </div>
        </div>

        {/* Explanation */}
        <div
          className={`mt-5 sm:mt-6 p-3 sm:p-4 rounded-lg text-xs sm:text-sm ${
            activeTab === 'good'
              ? 'bg-emerald-50 border border-emerald-200 text-emerald-800'
              : 'bg-red-50 border border-red-200 text-red-800'
          }`}
        >
          {activeTab === 'good' ? (
            <p>
              <strong>Sparse stacking:</strong> With stride-2 blocks, each power
              of 5 lands in its own 2-digit slot. The terms barely overlap, so
              the geometric structure nearly fits the decimal costume directly.
              Flux is a tiny adjustment.
            </p>
          ) : (
            <p>
              <strong>Collision catastrophe:</strong> With stride-1 blocks,
              every power of 10 lands in adjacent single-digit positions. The
              sum S massively overshoots R, requiring a huge negative flux to
              correct. The "natural" driver is the <em>worst</em> choice.
            </p>
          )}
        </div>
      </div>
    </div>
  );
};

export default FluxContrast;
