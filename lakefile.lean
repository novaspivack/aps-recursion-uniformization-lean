import Lake
open Lake DSL

package aps_recursion_uniformization_lean where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

-- Phase I: frozen theorem base
require aps_undecidability_interfaces_lean from "../aps-undecidability-interfaces-lean"
-- Phase II: recursion-composition uniformity (corrected exactness, regime bifurcation)
require aps_recursion_composition_uniformity_lean from "../aps-recursion-composition-uniformity-lean"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.29.0-rc6"

@[default_target]
lean_lib APSUniformization where
  roots := #[`APSUniformization]

lean_exe aps_recursion_uniformization_lean where
  root := `Main
