interface SectionDividerProps {
  part: string;
  title: string;
}

/**
 * Section divider for major document parts.
 * Displays a gradient background with part number and title.
 */
const SectionDivider = ({ part, title }: SectionDividerProps) => (
  <div className="my-12 sm:my-16 py-6 sm:py-8 border-y border-stone-300 bg-gradient-to-r from-stone-100 via-stone-50 to-stone-100">
    <div className="text-center">
      <span className="text-xs font-mono text-stone-400 uppercase tracking-widest">
        {part}
      </span>
      <h2 className="text-xl sm:text-2xl font-serif font-semibold text-stone-800 mt-2">
        {title}
      </h2>
    </div>
  </div>
);

export default SectionDivider;
