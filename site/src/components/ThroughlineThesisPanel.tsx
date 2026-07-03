import {
  claimById,
  featuredThroughline,
  orbitCarryFrontier,
  stateMergingCaseStudies,
  stateMergingFamilyStudies,
  theoremWitnessById,
} from '../lib/atlas';

const groupMeta: Record<
  keyof typeof orbitCarryFrontier,
  { title: string; tone: string }
> = {
  orbit_layer_examples: {
    title: 'Orbit Layer Examples',
    tone: 'border-emerald-200 bg-emerald-50 text-emerald-900',
  },
  carry_layer_examples: {
    title: 'Carry Layer Examples',
    tone: 'border-amber-200 bg-amber-50 text-amber-950',
  },
  frontier_targets: {
    title: 'Frontier Targets',
    tone: 'border-sky-200 bg-sky-50 text-sky-950',
  },
  obstruction_families: {
    title: 'Obstruction Surface',
    tone: 'border-rose-200 bg-rose-50 text-rose-950',
  },
};

const ThroughlineThesisPanel = () => {
  if (!featuredThroughline) {
    return null;
  }

  return (
    <section className="mb-8 sm:mb-10">
      <div className="rounded-sm border border-stone-200 bg-white p-4 shadow-sm sm:p-6">
        <div className="grid gap-6 xl:grid-cols-[1.15fr_1fr]">
          <div>
            <div className="text-xs font-bold uppercase tracking-[0.18em] text-stone-500">
              Research Thesis
            </div>
            <h2 className="mt-2 text-xl font-serif font-semibold text-stone-900 sm:text-2xl">
              {featuredThroughline.title}
            </h2>
            <p className="mt-3 text-sm leading-relaxed text-stone-700 sm:text-base">
              {featuredThroughline.headline}
            </p>
            <div className="mt-4 rounded-lg border border-sky-100 bg-sky-50 p-4 text-sm leading-relaxed text-sky-900">
              {featuredThroughline.status_note}
            </div>

            <div className="mt-4 rounded-lg border border-amber-100 bg-amber-50 p-4 text-sm text-amber-950">
              <div className="font-semibold">New finite-window surface</div>
              <p className="mt-2 leading-relaxed">
                The preimage-fiber profile (state-merging atlas) now sits beside
                the throughline as a bounded explanation surface: {stateMergingCaseStudies.length}{' '}
                canonical cases and {stateMergingFamilyStudies.length} canonical families
                make compression visible directly without promoting a global theorem.
              </p>
            </div>

            <div className="mt-5 grid gap-3 md:grid-cols-2">
              {featuredThroughline.ladder.map(entry => (
                <article
                  key={entry.id}
                  className="rounded-lg border border-stone-200 bg-stone-50 p-4"
                >
                  <div className="text-sm font-semibold text-stone-900">
                    {entry.label}
                  </div>
                  <p className="mt-2 text-sm leading-relaxed text-stone-700">
                    {entry.summary}
                  </p>
                  <div className="mt-3 text-xs text-stone-500">
                    Claims:{' '}
                    {entry.claim_ids
                      .map(id => claimById.get(id)?.title ?? id)
                      .join(' | ')}
                  </div>
                  <div className="mt-1 text-xs text-stone-500">
                    Witnesses: {entry.witness_ids.map(id => theoremWitnessById.get(id)?.label ?? id).join(' | ')}
                  </div>
                </article>
              ))}
            </div>
          </div>

          <div className="space-y-4">
            {(Object.keys(orbitCarryFrontier) as Array<keyof typeof orbitCarryFrontier>).map(groupKey => (
              <article key={groupKey} className="rounded-lg border border-stone-200 bg-stone-50 p-4">
                <div className="flex items-center justify-between gap-3">
                  <h3 className="text-sm font-bold uppercase tracking-wide text-stone-600">
                    {groupMeta[groupKey].title}
                  </h3>
                  <span className="text-xs text-stone-500">
                    {orbitCarryFrontier[groupKey].length} rows
                  </span>
                </div>
                <div className="mt-3 space-y-3">
                  {orbitCarryFrontier[groupKey].map(row => (
                    <div
                      key={`${groupKey}-${row.label}-${row.n ?? row.members?.join('-') ?? 'group'}`}
                      className={`rounded-lg border p-3 ${groupMeta[groupKey].tone}`}
                    >
                      <div className="flex flex-wrap items-center gap-2">
                        <div className="text-sm font-semibold">{row.label}</div>
                        {row.n ? (
                          <code className="rounded bg-white/80 px-2 py-1 text-[11px] text-stone-700">
                            1/{row.n}
                          </code>
                        ) : row.members?.length ? (
                          <code className="rounded bg-white/80 px-2 py-1 text-[11px] text-stone-700">
                            {row.members.join(' / ')}
                          </code>
                        ) : null}
                      </div>
                      <p className="mt-2 text-sm leading-relaxed">
                        {row.signal ?? row.summary ?? row.distinctive_feature ?? row.observed}
                      </p>
                      {'open_boundary' in row && row.open_boundary ? (
                        <div className="mt-2 text-xs text-stone-600">
                          Open boundary: {row.open_boundary}
                        </div>
                      ) : null}
                    </div>
                  ))}
                </div>
              </article>
            ))}
          </div>
        </div>
      </div>
    </section>
  );
};

export default ThroughlineThesisPanel;
