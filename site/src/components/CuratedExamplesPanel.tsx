import {
  bridgeHighlights,
  bridgeQ1Highlights,
  canonicalExamples,
  compositeHighlights,
  displayTerm,
  exampleAtlas,
  primeQRHighlights,
  searchPreview,
} from '../lib/atlas';

interface CuratedExamplesPanelProps {
  standardMode: boolean;
}

const CuratedExamplesPanel = ({ standardMode }: CuratedExamplesPanelProps) => {
  const leaderboardPreview = [
    {
      title: 'Readable bridges',
      entries: bridgeHighlights.slice(0, 3).map(entry => ({
        label: `1/${entry.n}`,
        detail: `m = ${entry.m}, k = ${entry.k}, q = ${entry.q}, period = ${entry.period}`,
      })),
    },
    {
      title: 'Pure q = 1 bridges',
      entries: bridgeQ1Highlights.slice(0, 3).map(entry => ({
        label: `1/${entry.n}`,
        detail: `m = ${entry.m}, k = ${entry.k}, visible prefix ${entry.visible_prefix}`,
      })),
    },
    {
      title: 'Composite CRT profiles',
      entries: compositeHighlights.slice(0, 3).map(entry => ({
        label: `1/${entry.n}`,
        detail: `M = ${entry.stripped_modulus}, preperiod = ${entry.preperiod_digits}, ord = ${entry.global_order}`,
      })),
    },
    {
      title: 'Prime QR examples',
      entries: primeQRHighlights.slice(0, 3).map(entry => ({
        label: `p = ${entry.p}`,
        detail: `stride = ${entry.preferred_stride}, k = ${entry.preferred_k}, count = ${entry.stride_count}`,
      })),
    },
  ];

  return (
    <section className="mb-8 sm:mb-10">
      <div className="mb-5">
        <h2 className="text-xs font-bold uppercase tracking-[0.18em] text-stone-500 mb-2">
          Curated Search Examples
        </h2>
        <p className="text-sm sm:text-base leading-relaxed text-stone-700 font-serif">
          Track 3 turned the search layer into a curated atlas. The site now
          points at those stable examples instead of improvising canonical cases
          in prose.
        </p>
      </div>

      <div className="grid gap-4 lg:grid-cols-[1.25fr_1fr]">
        <div className="rounded-sm border border-stone-200 bg-white p-4 sm:p-5 shadow-sm">
          <div className="flex flex-wrap items-center justify-between gap-3 mb-4">
            <h3 className="text-base sm:text-lg font-serif font-semibold text-stone-900">
              Canonical Atlas
            </h3>
            <span className="text-xs text-stone-500">
              schema {exampleAtlas.schema_version}, base {exampleAtlas.metadata.base}, top {exampleAtlas.metadata.top}
            </span>
          </div>
          <div className="space-y-3">
            {canonicalExamples.map(example => {
              const term = displayTerm(example.primary_vocabulary_id, standardMode);
              return (
                <article
                  key={`${example.category}-${example.n}`}
                  className="rounded-lg border border-stone-200 bg-stone-50 p-3"
                >
                  <div className="flex flex-wrap items-center gap-2">
                    <div className="text-sm font-semibold text-stone-900">
                      {example.label}
                    </div>
                    <code className="rounded bg-white px-2 py-1 text-xs text-stone-700">
                      1/{example.n}
                    </code>
                  </div>
                  <div className="mt-2 text-xs uppercase tracking-wide text-stone-500">
                    {standardMode ? 'Standard label' : 'Repo alias'}: {term.primary}
                    {term.secondary ? ` | ${standardMode ? 'Aliases' : 'Standard'}: ${term.secondary}` : ''}
                  </div>
                  <p className="mt-2 text-sm leading-relaxed text-stone-700">
                    {example.explanation}
                  </p>
                </article>
              );
            })}
          </div>
        </div>

        <div className="space-y-4">
          <aside className="rounded-sm border border-stone-200 bg-white p-4 shadow-sm">
            <h3 className="text-sm font-bold uppercase tracking-wide text-stone-500 mb-3">
              Search Commands
            </h3>
            <div className="space-y-3">
              {searchPreview.slice(0, 4).map(entry => (
                <article key={entry.label} className="rounded-lg border border-stone-200 bg-stone-50 p-3">
                  <div className="text-sm font-semibold text-stone-900">{entry.label}</div>
                  <p className="mt-2 text-sm leading-relaxed text-stone-700">{entry.summary}</p>
                  <code className="mt-2 block text-xs text-stone-500">{entry.command}</code>
                </article>
              ))}
            </div>
          </aside>

          <aside className="rounded-sm border border-stone-200 bg-white p-4 shadow-sm">
            <h3 className="text-sm font-bold uppercase tracking-wide text-stone-500 mb-3">
              Leaderboards
            </h3>
            <div className="space-y-3">
              {leaderboardPreview.map(group => (
                <article key={group.title} className="rounded-lg border border-stone-200 bg-stone-50 p-3">
                  <div className="text-sm font-semibold text-stone-900">{group.title}</div>
                  <div className="mt-2 space-y-2">
                    {group.entries.map(entry => (
                      <div key={`${group.title}-${entry.label}`} className="text-sm text-stone-700">
                        <span className="font-medium text-stone-900">{entry.label}</span>
                        {' '}
                        <span>{entry.detail}</span>
                      </div>
                    ))}
                  </div>
                </article>
              ))}
            </div>
          </aside>
        </div>
      </div>
    </section>
  );
};

export default CuratedExamplesPanel;
