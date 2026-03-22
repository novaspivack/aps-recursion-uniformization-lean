import APSUniformization.BaireSpaceOfDiagonals
import APSUniformization.FixedPointBasins
import APSUniformization.MeagernessOfBasins
import APSRecComp
import APSRecComp.SmnSectionSurjectivity
import APSMinimalInterface.Indexed
import APSMinimalInterface.InterfaceLattice
import Mathlib.Data.Nat.Pairing

/-!
# Baire Cover Argument — SPEC_V3 Module 4

The main argument connecting I_rec to Baire category:
I_rec ⇒ some basin is nonmeager ⇒ section surjectivity.

## Historical status

T10 (nonmeager basin ⇒ section surjectivity) depended on T6, which was **proved false**
(`T6Counterexample.lean`). T11 depended on T10. Both were part of the positive Baire route
for I_rec ⇒ I_comp, which is now known to be false (`Separation.lean`).
T10 and T11 are commented out. T9 is a genuine structural fact and is preserved.
-/

namespace APSUniformization

open Nat
open APSMinimalInterface
open APSRecComp
open Classical

/-! ## T9: I_rec implies nonmeager basin -/

/-- **T9:** Under I_rec, for representable d (with smn diagonal injective), some fixed-point basin is nonmeager. -/
theorem I_rec_implies_nonmeager_basin (aps : IndexedAPS)
    (h_rec : HasIRecIndexed aps) (d : ℕ → ℕ)
    (hd_rep : IndexedRepresentableUnary aps d)
    (h_smn_inj : Function.Injective (fun x => aps.smn x x)) :
    ∃ e, ¬ MeagerInFiber aps d (FixedPointBasin aps e d) := by
  obtain ⟨h₀, h₀_in⟩ := diagonal_fiber_nonempty_of_rep aps d hd_rep h_smn_inj
  by_contra h_no
  have h_all : ∀ e, MeagerInFiber aps d (FixedPointBasin aps e d) := fun e => by
    by_contra h_not; exact h_no ⟨e, h_not⟩
  obtain ⟨h, h_in, h_avoid⟩ := all_meager_not_covered aps d ⟨h₀, h₀_in⟩ h_all
  obtain ⟨e, he⟩ := I_rec_implies_basins_cover aps h_rec d hd_rep h h_in
  exact h_avoid e he

/-! ## T10: Nonmeager basin implies section surjectivity — DEPENDED ON T6 (FALSE)

T10 used the contrapositive of T6 (section failure ⇒ basin nowhere dense ⇒ meager).
T6 is false (`T6Counterexample.lean`), so T10 is unsound as stated.

-- theorem nonmeager_basin_implies_section_surj (aps : IndexedAPS) (e : ℕ) (d : ℕ → ℕ)
--     (h_nonmeager : ¬ MeagerInFiber aps d (FixedPointBasin aps e d)) :
--     SmnSectionSurjectiveAt aps e
-/

/-! ## T11: I_rec implies section surjectivity — DEPENDED ON T10

-- theorem I_rec_implies_section_surj (aps : IndexedAPS)
--     (h_rec : HasIRecIndexed aps) (d : ℕ → ℕ)
--     (hd_rep : IndexedRepresentableUnary aps d)
--     (h_smn_inj : Function.Injective (fun x => aps.smn x x)) :
--     ∃ x₀, SmnSectionSurjectiveAt aps x₀
-/

end APSUniformization
