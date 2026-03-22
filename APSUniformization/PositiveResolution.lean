import APSUniformization.BaireCoverArgument
import APSUniformization.MeagernessOfBasins
import APSRecComp
import APSRecComp.FiniteTracking
import APSRecComp.SmnSectionSurjectivity
import APSMinimalInterface.Indexed
import APSMinimalInterface.InterfaceLattice

/-!
# Positive Resolution — SPEC_V3 Module 5 (historical)

## Historical status

This module attempted to prove I_rec ⇒ I_comp via the Baire route.
The implication is now known to be **false** (`Separation.lean`).
T6 was proved false (`T6Counterexample.lean`), killing the Baire route.
All theorems here are commented out.

## T12a: I_rec + section surjectivity everywhere ⇒ I_comp
Gap was Uniform ⇒ Joint (circular: requires I_comp).

-- theorem I_rec_and_section_surj_implies_I_comp (aps : IndexedAPS)
--     (h_rec : HasIRecIndexed aps)
--     (h_surj : ∀ x₀, SmnSectionSurjectiveAt aps x₀) :
--     HasICompIndexed aps

## T12b: I_rec + T6 ⇒ I_comp (summit theorem)
Depended on T6 (false) and T10 (unsound).

-- theorem I_rec_implies_I_comp_via_baire (aps : IndexedAPS)
--     (h_rec : HasIRecIndexed aps)
--     (h_diag : HasIDiagIndexed aps)
--     (h_const : ∀ c, IndexedRepresentableUnary aps (fun _ => c))
--     (h_meager : ∀ x₀ e d, ¬ SmnSectionSurjectiveAt aps x₀ →
--       NowhereDenseInFiber aps d (FixedPointBasin aps e d)) :
--     HasICompIndexed aps

## T12 (conditional): I_rec ⇒ ∃ x₀, SmnSectionSurjectiveAt x₀
Depended on T10/T11 (unsound due to T6 being false).

-- theorem I_rec_implies_section_surj_some (aps : IndexedAPS)
--     (h_rec : HasIRecIndexed aps) (d : ℕ → ℕ)
--     (hd_rep : IndexedRepresentableUnary aps d)
--     (h_smn_inj : Function.Injective (fun x => aps.smn x x)) :
--     ∃ x₀, SmnSectionSurjectiveAt aps x₀ :=
--   I_rec_implies_section_surj aps h_rec d hd_rep h_smn_inj
-/

namespace APSUniformization
end APSUniformization
