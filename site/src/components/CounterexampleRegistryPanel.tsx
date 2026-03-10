import { claimById, featuredCounterexamples } from '../lib/atlas';

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

const CounterexampleRegistryPanel = () => {
  return (
    <section className="mb-8 sm:mb-10">
      <div className="mb-5">
        <h2 className="text-xs font-bold uppercase tracking-[0.18em] text-stone-500 mb-2">
          Counterexample Registry
        </h2>
        <p className="text-sm sm:text-base leading-relaxed text-stone-700 font-serif">
          The repo now keeps the failures of older prose visible. These examples
          are part of the public interface because they explain why the current
          statements are narrower and more exact.
        </p>
      </div>

      <div className="grid gap-4 lg:grid-cols-3">
        {featuredCounterexamples.map(counterexample => {
          const correctedClaim = claimById.get(counterexample.claim_id);
          return (
            <article
              key={counterexample.id}
              className="rounded-sm border border-rose-200 bg-white p-4 shadow-sm"
            >
              <div className="text-xs font-bold uppercase tracking-wide text-rose-700 mb-2">
                Legacy claim
              </div>
              <h3 className="text-base font-serif font-semibold text-stone-900">
                {counterexample.legacy_claim}
              </h3>
              <p className="mt-3 text-sm leading-relaxed text-stone-700">
                {counterexample.observed}
              </p>
              <div className="mt-4 rounded-lg border border-emerald-100 bg-emerald-50 p-3">
                <div className="text-[10px] font-bold uppercase tracking-wide text-emerald-700">
                  Replacement
                </div>
                <p className="mt-2 text-sm leading-relaxed text-emerald-900">
                  {counterexample.replacement}
                </p>
              </div>
              {correctedClaim && (
                <div className="mt-4 flex flex-wrap items-center gap-2 text-xs text-stone-500">
                  <code className="rounded bg-stone-100 px-2 py-1 text-stone-700">
                    {correctedClaim.id}
                  </code>
                  <span
                    className={`rounded-full px-2.5 py-1 font-bold uppercase tracking-wide ${statusStyles[correctedClaim.status]}`}
                  >
                    {statusLabel[correctedClaim.status]}
                  </span>
                </div>
              )}
            </article>
          );
        })}
      </div>
    </section>
  );
};

export default CounterexampleRegistryPanel;
