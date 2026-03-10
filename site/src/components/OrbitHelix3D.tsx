import { useRef, useMemo } from 'react';
import { Canvas, useFrame } from '@react-three/fiber';
import { OrbitControls, Line } from '@react-three/drei';
import * as THREE from 'three';
import { powMod, multiplicativeOrder } from '../lib/math';

interface OrbitHelix3DProps {
  /** Prime modulus */
  prime?: number;
  /** Number base */
  base?: number;
  /** Current animation step */
  currentStep?: number;
  /** Show both k and B helixes */
  showBothHelixes?: boolean;
  /** Height scale factor */
  heightScale?: number;
}

interface HelixPoint {
  position: [number, number, number];
  residue: number;
  integerValue: number;
  step: number;
}

const BASE_RADIUS = 2;
const CONE_HEIGHT = 4;

/**
 * Compute helix points for a sequence of powers on a cone surface
 */
function computeHelixPoints(
  prime: number,
  multiplier: number,
  orbitLength: number,
  _heightScale: number // kept for API compatibility but unused with cone
): HelixPoint[] {
  const points: HelixPoint[] = [];

  for (let i = 0; i <= orbitLength; i++) {
    const residue = i === 0 ? 1 : powMod(multiplier, i, prime);
    const integerValue = Math.pow(multiplier, i);

    // Progress from base (0) to apex (1)
    const progress = i / orbitLength;

    // Radius shrinks as we climb the cone (converges to apex)
    const radius = BASE_RADIUS * (1 - progress);

    // Height increases linearly with step
    const height = progress * CONE_HEIGHT;

    // Angle based on residue position on the mod p circle
    const angle = (residue / prime) * 2 * Math.PI - Math.PI / 2;

    points.push({
      position: [
        Math.cos(angle) * radius,
        height,
        Math.sin(angle) * radius,
      ],
      residue,
      integerValue,
      step: i,
    });
  }

  return points;
}

/**
 * Semi-transparent cone surface showing the "track"
 */
function ConeSurface({ opacity = 0.15 }: { opacity?: number }) {
  return (
    <mesh position={[0, CONE_HEIGHT / 2, 0]} rotation={[0, 0, 0]}>
      <coneGeometry args={[BASE_RADIUS, CONE_HEIGHT, 32, 1, true]} />
      <meshBasicMaterial
        color="#78716c"
        transparent
        opacity={opacity}
        side={THREE.DoubleSide}
        wireframe={false}
      />
    </mesh>
  );
}

/**
 * Mirror cone for flux visualization - inverted cone below the base
 * The flux "lives" in this shadow world, the correction needed for closure
 */
function FluxMirrorCone({
  opacity = 0.08,
  show = false,
  fluxRatio = 0.5 // Normalized flux (0-1) determines cone size
}: {
  opacity?: number;
  show?: boolean;
  fluxRatio?: number;
}) {
  if (!show) return null;

  // Mirror cone height proportional to flux
  const mirrorHeight = CONE_HEIGHT * Math.min(fluxRatio, 1) * 0.5;
  const mirrorRadius = BASE_RADIUS * Math.min(fluxRatio, 1) * 0.5;

  return (
    <group>
      {/* Inverted cone below base circle */}
      <mesh position={[0, -mirrorHeight / 2, 0]} rotation={[Math.PI, 0, 0]}>
        <coneGeometry args={[mirrorRadius, mirrorHeight, 32, 1, true]} />
        <meshBasicMaterial
          color="#f59e0b"
          transparent
          opacity={opacity}
          side={THREE.DoubleSide}
        />
      </mesh>
      {/* Flux apex marker */}
      <mesh position={[0, -mirrorHeight, 0]}>
        <sphereGeometry args={[0.08, 16, 16]} />
        <meshBasicMaterial color="#f59e0b" transparent opacity={0.6} />
      </mesh>
    </group>
  );
}

/**
 * Wireframe outline of the cone for better visibility
 */
function ConeWireframe() {
  const points = useMemo(() => {
    const pts: THREE.Vector3[] = [];
    const segments = 32;
    // Base circle
    for (let i = 0; i <= segments; i++) {
      const angle = (i / segments) * Math.PI * 2;
      pts.push(new THREE.Vector3(
        Math.cos(angle) * BASE_RADIUS,
        0,
        Math.sin(angle) * BASE_RADIUS
      ));
    }
    return pts;
  }, []);

  // Lines from base to apex
  const apexLines = useMemo(() => {
    const lines: THREE.Vector3[][] = [];
    const numLines = 8;
    for (let i = 0; i < numLines; i++) {
      const angle = (i / numLines) * Math.PI * 2;
      lines.push([
        new THREE.Vector3(Math.cos(angle) * BASE_RADIUS, 0, Math.sin(angle) * BASE_RADIUS),
        new THREE.Vector3(0, CONE_HEIGHT, 0),
      ]);
    }
    return lines;
  }, []);

  return (
    <group>
      <Line points={points} color="#a8a29e" lineWidth={1} />
      {apexLines.map((pts, i) => (
        <Line key={i} points={pts} color="#d6d3d1" lineWidth={0.5} opacity={0.5} transparent />
      ))}
    </group>
  );
}

/**
 * Check if a number is a quadratic residue mod p
 */
function isQuadraticResidue(n: number, p: number): boolean {
  if (n % p === 0) return false;
  // Euler's criterion: n^((p-1)/2) ≡ 1 (mod p) iff n is QR
  return powMod(n, (p - 1) / 2, p) === 1;
}

/**
 * The base platform showing mod p circle with residue markers
 */
function BasePlatform({ prime }: { prime: number }) {
  // Create residue markers on the base circle
  const residueMarkers = useMemo(() => {
    const markers: { position: [number, number, number]; isQR: boolean; value: number }[] = [];
    for (let r = 1; r < prime; r++) {
      const angle = (r / prime) * 2 * Math.PI - Math.PI / 2;
      markers.push({
        position: [Math.cos(angle) * BASE_RADIUS, 0, Math.sin(angle) * BASE_RADIUS],
        isQR: isQuadraticResidue(r, prime),
        value: r,
      });
    }
    return markers;
  }, [prime]);

  return (
    <group>
      {/* Residue markers */}
      {residueMarkers.map(({ position, isQR, value }) => (
        <mesh key={value} position={position}>
          {isQR ? (
            <octahedronGeometry args={[0.08, 0]} />
          ) : (
            <sphereGeometry args={[0.05, 8, 8]} />
          )}
          <meshBasicMaterial color={isQR ? '#8b5cf6' : '#fda4af'} />
        </mesh>
      ))}

      {/* Starting point marker for "1" */}
      <mesh position={[BASE_RADIUS, 0, 0]}>
        <sphereGeometry args={[0.1, 16, 16]} />
        <meshBasicMaterial color="#10b981" />
      </mesh>

      {/* Apex marker */}
      <mesh position={[0, CONE_HEIGHT, 0]}>
        <sphereGeometry args={[0.08, 16, 16]} />
        <meshBasicMaterial color="#f59e0b" />
      </mesh>
    </group>
  );
}

/**
 * A single helix (k or B)
 */
function Helix({
  points,
  color,
  currentStep,
  showFilaments = false,
  otherPoints,
}: {
  points: HelixPoint[];
  color: string;
  currentStep: number;
  showFilaments?: boolean;
  otherPoints?: HelixPoint[];
}) {
  const visiblePoints = points.slice(0, Math.min(currentStep + 1, points.length));

  // Create line points for the helix path
  const linePoints = useMemo(() => {
    return visiblePoints.map((p) => new THREE.Vector3(...p.position));
  }, [visiblePoints]);

  // Create filament points (connecting to other helix)
  const filaments = useMemo(() => {
    if (!showFilaments || !otherPoints) return [];
    return visiblePoints.map((p, i) => {
      if (i >= otherPoints.length) return null;
      return [
        new THREE.Vector3(...p.position),
        new THREE.Vector3(...otherPoints[i].position),
      ];
    }).filter(Boolean) as THREE.Vector3[][];
  }, [visiblePoints, otherPoints, showFilaments]);

  return (
    <group>
      {/* Helix path */}
      {linePoints.length > 1 && (
        <Line points={linePoints} color={color} lineWidth={2} />
      )}

      {/* Point markers */}
      {visiblePoints.map((point, i) => {
        const isCurrent = i === visiblePoints.length - 1;
        return (
          <mesh key={i} position={point.position}>
            <sphereGeometry args={[isCurrent ? 0.12 : 0.06, 16, 16]} />
            <meshBasicMaterial color={color} transparent opacity={isCurrent ? 1 : 0.7} />
          </mesh>
        );
      })}

      {/* Current position glow */}
      {visiblePoints.length > 0 && (
        <mesh position={visiblePoints[visiblePoints.length - 1].position}>
          <sphereGeometry args={[0.2, 16, 16]} />
          <meshBasicMaterial color={color} transparent opacity={0.3} />
        </mesh>
      )}

      {/* Filaments */}
      {filaments.map((pts, i) => (
        <Line key={`fil-${i}`} points={pts} color="#d6d3d1" lineWidth={1} />
      ))}
    </group>
  );
}

/**
 * Camera that frames the cone nicely
 */
function CameraRig() {
  const controlsRef = useRef<any>(null);

  // Fixed target: center of the cone
  const targetY = CONE_HEIGHT / 2;

  useFrame(() => {
    if (controlsRef.current) {
      // Gentle auto-rotation
      controlsRef.current.autoRotate = true;
      controlsRef.current.autoRotateSpeed = 0.3;

      // Keep looking at cone center
      controlsRef.current.target.y = targetY;
    }
  });

  return (
    <OrbitControls
      ref={controlsRef}
      enablePan={false}
      minDistance={4}
      maxDistance={15}
      maxPolarAngle={Math.PI * 0.85}
      target={[0, targetY, 0]}
    />
  );
}

/**
 * Main 3D scene
 */
function Scene({
  prime,
  base,
  currentStep,
  showBothHelixes,
  heightScale,
}: Required<Omit<OrbitHelix3DProps, 'showBothHelixes'>> & { showBothHelixes: boolean }) {
  // Compute k = base mod prime
  const k = base % prime;
  const orbitLength = multiplicativeOrder(k, prime);

  // Compute helix points
  const kPoints = useMemo(
    () => computeHelixPoints(prime, k, orbitLength, heightScale),
    [prime, k, orbitLength, heightScale]
  );

  const bPoints = useMemo(
    () => computeHelixPoints(prime, base, orbitLength, heightScale),
    [prime, base, orbitLength, heightScale]
  );

  // Compute flux ratio for mirror cone visualization
  // F = (k^L - 1) / p, normalized by comparing to reptend R = (B^L - 1) / p
  const fluxRatio = useMemo(() => {
    if (orbitLength === 0) return 0;
    // Use BigInt for large numbers
    const kL = BigInt(k) ** BigInt(orbitLength);
    const BL = BigInt(base) ** BigInt(orbitLength);
    const p = BigInt(prime);
    const F = (kL - 1n) / p;
    const R = (BL - 1n) / p;
    if (R === 0n) return 0;
    // Flux as fraction of reptend (how much of R is "correction")
    return Math.min(1, Number(F) / Number(R));
  }, [k, base, prime, orbitLength]);

  return (
    <>
      <ambientLight intensity={0.6} />
      <pointLight position={[10, 10, 10]} intensity={0.8} />

      {/* Cone surface and wireframe */}
      <ConeSurface opacity={0.1} />
      <ConeWireframe />

      {/* Flux mirror cone - appears at closure, inverted below base */}
      <FluxMirrorCone
        show={currentStep >= orbitLength}
        fluxRatio={fluxRatio}
        opacity={0.15}
      />

      {/* Base platform with residue markers */}
      <BasePlatform prime={prime} />

      {/* Helix k (skeleton - green) */}
      <Helix
        points={kPoints}
        color="#10b981"
        currentStep={currentStep}
        showFilaments={showBothHelixes}
        otherPoints={showBothHelixes ? bPoints : undefined}
      />

      {/* Helix B (base - indigo) */}
      {showBothHelixes && (
        <Helix points={bPoints} color="#6366f1" currentStep={currentStep} />
      )}

      {/* At closure, highlight the apex where both helixes meet */}
      {currentStep >= orbitLength && (
        <mesh position={[0, CONE_HEIGHT, 0]}>
          <sphereGeometry args={[0.15, 16, 16]} />
          <meshBasicMaterial color="#f59e0b" transparent opacity={0.8} />
        </mesh>
      )}

      {/* Camera */}
      <CameraRig />
    </>
  );
}

/**
 * 3D Orbital visualization showing the dual helix structure of reptend orbits.
 *
 * The two helixes represent:
 * - Green (k): The skeleton orbit - powers of k = base mod p
 * - Blue (B): The base orbit - powers of the base itself
 *
 * Both visit the same positions mod p (same circular track) but at different
 * heights (different integer values). The flux gap at closure shows the
 * "cost" of the orbit returning to 1.
 */
const OrbitHelix3D = ({
  prime = 19,
  base = 10,
  currentStep = 0,
  showBothHelixes = true,
  heightScale = 0.15,
}: OrbitHelix3DProps) => {
  const k = base % prime;
  const orbitLength = multiplicativeOrder(k, prime);

  return (
    <div className="w-full aspect-square max-w-lg mx-auto bg-stone-900 rounded-xl overflow-hidden">
      <Canvas camera={{ position: [5, 4, 5], fov: 60 }}>
        <Scene
          prime={prime}
          base={base}
          currentStep={currentStep}
          showBothHelixes={showBothHelixes}
          heightScale={heightScale}
        />
      </Canvas>

      {/* Info overlay */}
      <div className="absolute bottom-2 left-2 right-2 flex justify-between items-end pointer-events-none">
        <div className="text-[10px] font-mono text-stone-400 bg-stone-900/80 px-2 py-1 rounded">
          <span className="text-emerald-400">●</span> k={k}{' '}
          {showBothHelixes && (
            <>
              <span className="text-indigo-400 ml-2">●</span> B={base}
            </>
          )}
        </div>
        <div className="text-[10px] font-mono text-stone-400 bg-stone-900/80 px-2 py-1 rounded">
          Step {currentStep}/{orbitLength}
        </div>
      </div>
    </div>
  );
};

export default OrbitHelix3D;
