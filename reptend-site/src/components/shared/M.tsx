import { ReactNode } from 'react';

interface MProps {
  children: ReactNode;
}

/**
 * Inline math formatting component.
 * Wraps content in monospace font for mathematical expressions.
 */
const M = ({ children }: MProps) => (
  <span className="font-mono text-stone-800 mx-0.5">{children}</span>
);

export default M;
