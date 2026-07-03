import { factorize, powMod } from './math';

export interface Point {
  x: number;
  y: number;
}

export function primitiveRoots(prime: number): number[] {
  const phi = prime - 1;
  const primeFactors = Array.from(factorize(phi).keys());
  const out: number[] = [];

  for (let candidate = 2; candidate < prime; candidate++) {
    const isPrimitive = primeFactors.every((q) => powMod(candidate, phi / q, prime) !== 1);
    if (isPrimitive) {
      out.push(candidate);
    }
  }

  return out;
}

export function buildDiscreteLogTable(
  generator: number,
  prime: number,
): {
  residueByExponent: number[];
  exponentByResidue: Map<number, number>;
} {
  const residueByExponent: number[] = [];
  const exponentByResidue = new Map<number, number>();
  let current = 1;

  for (let exponent = 0; exponent < prime - 1; exponent++) {
    residueByExponent.push(current);
    exponentByResidue.set(current, exponent);
    current = (current * generator) % prime;
  }

  return { residueByExponent, exponentByResidue };
}

export function pointOnUnitCircle(
  exponent: number,
  period: number,
  radius: number,
  center: Point = { x: 140, y: 140 },
): Point {
  const angle = -Math.PI / 2 + (2 * Math.PI * exponent) / period;
  return {
    x: center.x + Math.cos(angle) * radius,
    y: center.y + Math.sin(angle) * radius,
  };
}

export function pathFromPoints(points: Point[], closed: boolean = false): string {
  if (points.length === 0) {
    return '';
  }

  const commands = [`M ${points[0].x} ${points[0].y}`];
  for (let index = 1; index < points.length; index++) {
    commands.push(`L ${points[index].x} ${points[index].y}`);
  }
  if (closed) {
    commands.push('Z');
  }
  return commands.join(' ');
}
