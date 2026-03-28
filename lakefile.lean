import Lake
open Lake DSL

package aps_recursion_uniformization_lean where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

-- Phase I: frozen theorem base
require aps_undecidability_interfaces_lean from git
  "https://github.com/novaspivack/aps-undecidability-interfaces-lean.git"
  @ "e71766e41b0e97b93d5c36d7c0994fdbfc01cb83"

-- Phase II: recursion-composition uniformity (corrected exactness, regime bifurcation)
require aps_recursion_composition_uniformity_lean from git
  "https://github.com/novaspivack/aps-recursion-composition-uniformity-lean.git"
  @ "2d075bd71c14fe57105d362c8c3b5c43deeda3fe"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.29.0-rc6"

@[default_target]
lean_lib APSUniformization where
  roots := #[`APSUniformization]

lean_exe aps_recursion_uniformization_lean where
  root := `Main
