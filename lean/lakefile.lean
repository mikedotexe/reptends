import Lake
open Lake DSL

package «finite-reptends» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.26.0-rc2"

@[default_target]
lean_lib QRTour where
  srcDir := "."

lean_lib GeometricStack where
  srcDir := "."
