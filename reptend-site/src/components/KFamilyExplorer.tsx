import { useState } from 'react';
import {
  analyzeKFamily,
  formatFactorization,
  isQRGenerator,
  multiplicativeOrder,
  computeReptend,
  KFamilyEntry
} from '../lib/math';

const K_VALUES = [3, 4, 5, 7, 9, 11];

interface PrimeDetailProps {
  k: number;
  prime: number;
  onClose: () => void;
}

const PrimeDetail = ({ k, prime, onClose }: PrimeDetailProps) => {
  const order = multiplicativeOrder(k, prime);
  const isQRGen = isQRGenerator(k, prime);
  const reptend = computeReptend(prime);

  // Find m where 10^m ≡ k (mod p)
  let mValue: number | null = null;
  for (let m = 1; m <= 10; m++) {
    if (Math.pow(10, m) % prime === k % prime) {
      mValue = m;
      break;
    }
  }

  return (
    <div className="fixed inset-0 bg-black/50 flex items-center justify-center p-4 z-50">
      <div className="bg-stone-100 rounded-lg shadow-xl max-w-lg w-full p-4 sm:p-6">
        <div className="flex justify-between items-start mb-4">
          <h3 className="text-base sm:text-lg font-serif font-medium text-stone-900">
            Prime {prime} in the k={k} family
          </h3>
          <button
            onClick={onClose}
            className="text-stone-400 hover:text-stone-600 text-xl leading-none min-h-[44px] min-w-[44px] flex items-center justify-center -mr-2 -mt-2"
          >
            &times;
          </button>
        </div>

        <div className="space-y-4 text-stone-700 text-sm sm:text-base">
          <div className="bg-stone-200 rounded px-3 sm:px-4 py-3 font-mono text-xs sm:text-sm space-y-1">
            {mValue && (
              <div>10<sup>{mValue}</sup> &equiv; {k} (mod {prime})</div>
            )}
            <div>ord<sub>{prime}</sub>({k}) = {order}</div>
            <div>(p-1)/2 = {(prime - 1) / 2}</div>
          </div>

          <div>
            <span className="font-medium">QR-Generator: </span>
            {isQRGen ? (
              <span className="text-green-700">Yes &mdash; k={k} generates all quadratic residues</span>
            ) : (
              <span className="text-stone-500">No &mdash; order {order} &ne; {(prime - 1) / 2}</span>
            )}
          </div>

          <div>
            <div className="font-medium mb-1">Reptend of 1/{prime}:</div>
            <div className="font-mono text-xs sm:text-sm bg-stone-200 rounded px-3 py-2 break-all overflow-x-auto">
              0.{reptend}...
            </div>
            <div className="text-xs text-stone-500 mt-1">
              Period: {reptend.length} digits
            </div>
          </div>
        </div>
      </div>
    </div>
  );
};

interface FamilyTableProps {
  k: number;
  entries: KFamilyEntry[];
  onPrimeClick: (prime: number) => void;
}

const FamilyTable = ({ k, entries, onPrimeClick }: FamilyTableProps) => (
  <div className="overflow-x-auto -mx-4 sm:mx-0">
    <table className="w-full text-xs sm:text-sm border-collapse bg-stone-50 rounded min-w-[500px]">
      <thead>
        <tr className="border-b border-stone-300 bg-stone-200">
          <th className="py-2 px-2 sm:px-3 text-left font-medium text-stone-600">m</th>
          <th className="py-2 px-2 sm:px-3 text-left font-medium text-stone-600">10<sup>m</sup> - {k}</th>
          <th className="py-2 px-2 sm:px-3 text-left font-medium text-stone-600">Factorization</th>
          <th className="py-2 px-2 sm:px-3 text-left font-medium text-stone-600">QR-Gen Primes</th>
        </tr>
      </thead>
      <tbody className="font-mono text-stone-700">
        {entries.map((entry) => (
          <tr key={entry.m} className="border-b border-stone-200 hover:bg-stone-100 transition-colors">
            <td className="py-2 px-2 sm:px-3">{entry.m}</td>
            <td className="py-2 px-2 sm:px-3">{entry.composite.toLocaleString()}</td>
            <td className="py-2 px-2 sm:px-3">{formatFactorization(entry.composite)}</td>
            <td className="py-2 px-2 sm:px-3">
              {entry.primes.map((p, i) => (
                <span key={p.prime}>
                  {i > 0 && ', '}
                  <button
                    onClick={() => onPrimeClick(p.prime)}
                    className={`hover:underline min-h-[32px] ${
                      p.isQRGen
                        ? 'text-green-700 font-semibold'
                        : 'text-stone-500'
                    }`}
                  >
                    {p.prime}
                    {p.isQRGen && ' ✓'}
                  </button>
                </span>
              ))}
            </td>
          </tr>
        ))}
      </tbody>
    </table>
  </div>
);

const KFamilyExplorer = () => {
  const [selectedK, setSelectedK] = useState(5);
  const [selectedPrime, setSelectedPrime] = useState<number | null>(null);

  const entries = analyzeKFamily(selectedK, 7);

  return (
    <section className="mb-8 sm:mb-10">
      <h2 className="text-lg sm:text-xl font-serif font-bold text-stone-900 mb-3 sm:mb-4">
        Interactive: k-Family Explorer
      </h2>

      <p className="text-stone-700 leading-relaxed mb-4 text-sm sm:text-base">
        Choose a distance <span className="font-mono">k</span> to explore the family of composites{' '}
        <span className="font-mono">10<sup>m</sup> - k</span>. Primes marked with{' '}
        <span className="text-green-700 font-semibold">✓</span> have{' '}
        <span className="font-mono">k</span> as a QR-generator.
      </p>

      {/* K selector */}
      <div className="flex flex-wrap gap-2 mb-4">
        {K_VALUES.map((k) => (
          <button
            key={k}
            onClick={() => setSelectedK(k)}
            className={`px-3 sm:px-4 py-2 min-h-[44px] rounded font-mono text-xs sm:text-sm transition-colors ${
              k === selectedK
                ? 'bg-stone-800 text-stone-100'
                : 'bg-stone-200 text-stone-700 hover:bg-stone-300'
            }`}
          >
            k = {k}
          </button>
        ))}
      </div>

      {/* Key relationship display */}
      <div className="bg-stone-200 rounded px-3 sm:px-4 py-3 mb-4 font-mono text-xs sm:text-sm">
        <div className="text-stone-600 mb-1">The Distance Principle for k = {selectedK}:</div>
        <div className="text-stone-800 flex flex-col sm:flex-row sm:items-center gap-1 sm:gap-4">
          <span>10<sup>m</sup> - {selectedK} &rArr; 10<sup>m</sup> &equiv; {selectedK} (mod p)</span>
          <span className="text-stone-500 text-[10px] sm:text-xs">for each prime p dividing the composite</span>
        </div>
      </div>

      {/* Results table */}
      <FamilyTable
        k={selectedK}
        entries={entries}
        onPrimeClick={setSelectedPrime}
      />

      {/* Legend */}
      <div className="mt-3 text-[10px] sm:text-xs text-stone-500">
        <span className="text-green-700 font-semibold">✓</span> = QR-generator
        (ord<sub>p</sub>(k) = (p-1)/2) &mdash; Click any prime for details
      </div>

      {/* Prime detail modal */}
      {selectedPrime && (
        <PrimeDetail
          k={selectedK}
          prime={selectedPrime}
          onClose={() => setSelectedPrime(null)}
        />
      )}
    </section>
  );
};

export default KFamilyExplorer;
