import { ReactNode } from 'react';

interface BlockProps {
  children: ReactNode;
}

/**
 * Block-level math display component.
 * Centers content with monospace font, responsive text sizing.
 */
const Block = ({ children }: BlockProps) => (
  <div className="my-4 py-3 text-center font-mono text-stone-800 text-base sm:text-lg overflow-x-auto">
    {children}
  </div>
);

export default Block;
