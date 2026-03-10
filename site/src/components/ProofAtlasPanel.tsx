import { claimRegistry, featuredClaims, featuredCounterexamples, openClaims, searchPreview } from '../lib/atlas';

const statusStyles: Record<string, string> = {
  classical: 'bg-stone-200 text-stone-700',
  'reproved-here': 'bg-emerald-100 text-emerald-800',
  'implemented-here': 'bg-amber-100 text-amber-900',
  empirical: 'bg-rose-100 text-rose-800',
  open: 'bg-sky-100 text-sky-800',
};

const statusLabel: Record<string, string> = {
  classical: 'Classical',
  'reproved-here': 'Reproved Here',
  'implemented-here': 'Implemented Here',
  empirical: 'Empirical',
  open: 'Open',
};

const ProofAtlasPanel = () => {
  return (
    <section className="mb-8 sm:mb-10">
      <div className="bg-stone-900 text-stone-100 rounded-sm p-4 sm:p-6 border border-stone-800 shadow-sm mb-6">
        <h2 className="text-xs font-bold uppercase tracking-[0.18em] text-stone-300 mb-3">
          Claim Atlas
        </h2>
        <p className="text-sm sm:text-base leading-relaxed text-stone-100 font-serif">
          The project now distinguishes theorem status from visualization language. Claims are
          tagged as classical, reproved here, implemented here, empirical, or open. The site’s
          narrative should be read through that lens.
        </p>
        <p className="mt-3 text-xs text-stone-400">
          Registry entries: {claimRegistry.length} claims, {openClaims.length} open claims, {featuredCounterexamples.length} featured counterexamples
        </p>
      </div>

      <div className="grid gap-4 lg:grid-cols-[1.4fr_1fr]">
        <div className="space-y-4">
          {featuredClaims.map(claim => (
            <article key={claim.id} className="rounded-sm border border-stone-200 bg-white p-4 sm:p-5 shadow-sm">
              <div className="flex flex-wrap items-center gap-3 mb-3">
                <h3 className="text-base sm:text-lg font-serif font-semibold text-stone-900">
                  {claim.title}
                </h3>
                <span className={`rounded-full px-2.5 py-1 text-[10px] font-bold uppercase tracking-wide ${statusStyles[claim.status]}`}>
                  {statusLabel[claim.status]}
                </span>
              </div>
              <p className="text-sm sm:text-base leading-relaxed text-stone-700">{claim.statement}</p>
              <div className="mt-3 text-xs text-stone-500">
                Repo status: {claim.repo_status}
              </div>
              <div className="mt-1 text-xs text-stone-500">
                Proof status: {claim.proof_status}
              </div>
            </article>
          ))}
        </div>

        <div className="space-y-4">
          <aside className="rounded-sm border border-stone-200 bg-white p-4 shadow-sm">
            <h3 className="text-sm font-bold uppercase tracking-wide text-stone-500 mb-3">
              Open Claims
            </h3>
            <div className="space-y-3">
              {openClaims.map(claim => (
                <article key={claim.id} className="rounded-lg border border-sky-100 bg-sky-50 p-3">
                  <div className="flex items-center gap-2 mb-2">
                    <span className={`rounded-full px-2.5 py-1 text-[10px] font-bold uppercase tracking-wide ${statusStyles[claim.status]}`}>
                      {statusLabel[claim.status]}
                    </span>
                    <code className="text-xs text-sky-800">{claim.id}</code>
                  </div>
                  <div className="text-sm font-semibold text-sky-900">{claim.title}</div>
                  <p className="mt-2 text-sm leading-relaxed text-sky-800">{claim.statement}</p>
                </article>
              ))}
            </div>
          </aside>

          <aside className="rounded-sm border border-stone-200 bg-white p-4 shadow-sm">
            <h3 className="text-sm font-bold uppercase tracking-wide text-stone-500 mb-3">
              Counterexamples
            </h3>
            <div className="space-y-3">
              {featuredCounterexamples.map(counterexample => (
                <article key={counterexample.id} className="rounded-lg border border-rose-100 bg-rose-50 p-3">
                  <div className="text-sm font-semibold text-rose-900">{counterexample.legacy_claim}</div>
                  <p className="mt-2 text-sm leading-relaxed text-rose-800">{counterexample.observed}</p>
                </article>
              ))}
            </div>
          </aside>

          <aside className="rounded-sm border border-stone-200 bg-white p-4 shadow-sm">
            <h3 className="text-sm font-bold uppercase tracking-wide text-stone-500 mb-3">
              Search Outputs
            </h3>
            <div className="space-y-3">
              {searchPreview.map(entry => (
                <article key={entry.label} className="rounded-lg border border-stone-200 bg-stone-50 p-3">
                  <div className="text-sm font-semibold text-stone-900">{entry.label}</div>
                  <p className="mt-2 text-sm leading-relaxed text-stone-700">{entry.summary}</p>
                  <code className="mt-2 block text-xs text-stone-500">{entry.command}</code>
                </article>
              ))}
            </div>
          </aside>
        </div>
      </div>
    </section>
  );
};

export default ProofAtlasPanel;
