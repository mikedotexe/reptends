import { vocabulary } from '../lib/atlas';

interface StandardTerminologyPanelProps {
  standardMode: boolean;
  onToggle: () => void;
}

const StandardTerminologyPanel = ({
  standardMode,
  onToggle,
}: StandardTerminologyPanelProps) => {
  return (
    <section className="mb-8 sm:mb-10 bg-white p-4 sm:p-6 rounded-sm shadow-sm border border-stone-200">
      <div className="flex flex-col gap-4 sm:flex-row sm:items-start sm:justify-between mb-5">
        <div>
          <h2 className="text-xs font-bold text-stone-500 uppercase tracking-wide mb-2">
            Standard Terminology Mode
          </h2>
          <p className="text-stone-700 text-sm sm:text-base leading-relaxed font-serif">
            The site now keeps coined labels as optional aliases. Turn standard mode on to
            place the classical label first everywhere in this guide section.
          </p>
        </div>
        <button
          type="button"
          onClick={onToggle}
          className="shrink-0 rounded-full border border-stone-300 px-4 py-2 text-xs font-semibold uppercase tracking-wide text-stone-700 hover:bg-stone-100 transition-colors"
        >
          {standardMode ? 'Standard labels first' : 'Alias labels first'}
        </button>
      </div>

      <div className="grid gap-3 sm:grid-cols-2">
        {vocabulary.map(entry => {
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
    </section>
  );
};

export default StandardTerminologyPanel;
