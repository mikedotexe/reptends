import { useState } from 'react';
import { vocabulary } from '../lib/atlas';

interface StandardTerminologyPanelProps {
  standardMode: boolean;
  onToggle: () => void;
}

const StandardTerminologyPanel = ({
  standardMode,
  onToggle,
}: StandardTerminologyPanelProps) => {
  const [showAll, setShowAll] = useState(false);
  const featuredIds = new Set([
    'quotient_q',
    'remainder_k',
    'skeleton',
    'carry_layer',
    'preimage_fiber_profile',
    'remainder_orbit',
  ]);
  const visibleVocabulary = showAll
    ? vocabulary
    : vocabulary.filter(entry => featuredIds.has(entry.id));

  return (
    <section className="mb-8 sm:mb-10 bg-white p-4 sm:p-6 rounded-sm shadow-sm border border-stone-200">
      <div className="flex flex-col gap-4 sm:flex-row sm:items-start sm:justify-between mb-5">
        <div>
          <h2 className="text-xs font-bold text-stone-500 uppercase tracking-wide mb-2">
            Terminology Surface
          </h2>
          <p className="text-stone-700 text-sm sm:text-base leading-relaxed font-serif">
            This is now a lighter glossary surface. It shows the most important
            standard labels first, with the full vocabulary available on demand.
          </p>
        </div>
        <div className="flex flex-wrap gap-2">
          <button
            type="button"
            onClick={onToggle}
            className="shrink-0 rounded-full border border-stone-300 px-4 py-2 text-xs font-semibold uppercase tracking-wide text-stone-700 hover:bg-stone-100 transition-colors"
          >
            {standardMode ? 'Standard labels first' : 'Alias labels first'}
          </button>
          <button
            type="button"
            onClick={() => setShowAll(value => !value)}
            className="shrink-0 rounded-full border border-stone-300 px-4 py-2 text-xs font-semibold uppercase tracking-wide text-stone-700 hover:bg-stone-100 transition-colors"
          >
            {showAll ? 'Show key terms' : 'Show full glossary'}
          </button>
        </div>
      </div>

      <div className="grid gap-3 sm:grid-cols-2">
        {visibleVocabulary.map(entry => {
          const primary = standardMode ? entry.preferred_label : entry.repo_aliases[0];
          const secondary = standardMode
            ? entry.repo_aliases.join(', ')
            : entry.preferred_label;
          return (
            <article key={entry.id} className="rounded-lg border border-stone-200 bg-stone-50 p-4">
              <div className="text-sm font-semibold text-stone-900">{primary}</div>
              <div className="mt-1 text-xs uppercase tracking-wide text-stone-500">
                {standardMode ? 'Repo aliases' : 'Standard label'}: {secondary}
              </div>
              <p className="mt-3 text-sm leading-relaxed text-stone-700">{entry.meaning}</p>
              <div className="mt-3 text-xs text-stone-500">Scope: {entry.scope}</div>
            </article>
          );
        })}
      </div>

      {!showAll ? (
        <div className="mt-4 rounded-lg border border-stone-200 bg-stone-50 p-3 text-sm leading-relaxed text-stone-700">
          The full glossary includes {vocabulary.length} registry-backed vocabulary entries.
        </div>
      ) : null}
    </section>
  );
};

export default StandardTerminologyPanel;
