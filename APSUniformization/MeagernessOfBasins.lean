import APSUniformization.BaireSpaceOfDiagonals
import APSUniformization.FixedPointBasins
import APSRecComp
import APSRecComp.CardinalityArgument
import APSRecComp.SmnSectionSurjectivity
import APSRecComp.SmnReachability
import APSMinimalInterface.Indexed
import APSMinimalInterface.InterfaceLattice
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Finset.Basic

/-!
# Meagerness of Basins — SPEC_V3 Module 3

Core meagerness analysis: when section surjectivity or tracking fails,
fixed-point basins are "small" (nowhere dense / meager).

## Historical status

T6 (section failure ⇒ basin nowhere dense) was **proved false** in `T6Counterexample.lean`.
T7 depended on T6. Both were part of the positive Baire route for I_rec ⇒ I_comp,
which is now known to be false (`Separation.lean`). The sorry theorems are commented out.
T8 (Baire lemma) and T7a (reduction) are genuine structural facts and are preserved.
-/

namespace APSUniformization

open Nat
open APSMinimalInterface
open APSRecComp
open Classical

/-! ## T6: Section failure implies meager basin — PROVED FALSE

T6 as stated is false: `T6Counterexample.lean` shows that when e is on the diagonal
and the basin is the whole fiber, the basin is NOT nowhere dense. The two sorry branches
below were exactly the cases where T6 fails. The positive Baire route (T6 → T10 → T12)
is dead; the separation theorem (`Separation.lean`) confirms I_rec ⇏ I_comp.

-- theorem section_failure_implies_meager_basin (aps : IndexedAPS) (x₀ e : ℕ) (d : ℕ → ℕ)
--     (h_fail : ¬ SmnSectionSurjectiveAt aps x₀) :
--     NowhereDenseInFiber aps d (FixedPointBasin aps e d)
--
-- Unprovable branches: (1) e ∈ DiagonalRange, basin nonempty ⇒ basin = whole fiber.
-- (2) e ∈ F, h₀(e) ≃ e ⇒ cylinder ⊆ basin. T6 is false in these cases (T6Counterexample.lean).
-/

/-! ## T7: Tracking failure implies meager basins — DEPENDED ON T6

-- theorem tracking_failure_implies_meager_basins (aps : IndexedAPS) (h₀ : ℕ → ℕ) (d : ℕ → ℕ)
--     (h_ntrack : ¬ SmnReachable aps h₀) :
--     ∀ e, NowhereDenseInFiber aps d (FixedPointBasin aps e d)
--
-- T7 required T6 + quantifier swap (tracking failure ⇒ ∃ x₀, section failure at x₀).
-- T6 is false, so T7 as stated cannot be proved via this route.
-- T7a (reduction below) is still a valid structural fact.
-/

-- **T7a (reduction, commented out):** If section failure holds at some x₀, then every basin
-- is nowhere dense (assuming T6 held). Depends on T6, which is false.
-- theorem section_failure_some_implies_all_basins_meager (aps : IndexedAPS) (x₀ : ℕ) (d : ℕ → ℕ)
--     (h_fail : ¬ SmnSectionSurjectiveAt aps x₀) :
--     ∀ e, NowhereDenseInFiber aps d (FixedPointBasin aps e d) :=
--   fun e => section_failure_implies_meager_basin aps x₀ e d h_fail

/-! ## T8: All meager ⇒ fiber not covered (Baire) -/

/-- **T8:** If every basin is meager, the countable union of basins cannot cover the fiber. -/
theorem all_meager_not_covered (aps : IndexedAPS) (d : ℕ → ℕ)
    (h_ne : (DiagonalFiber aps d).Nonempty)
    (hm : ∀ e, MeagerInFiber aps d (FixedPointBasin aps e d)) :
    ∃ h ∈ DiagonalFiber aps d, ∀ e, h ∉ FixedPointBasin aps e d := by
  obtain ⟨h₀, h₀_in⟩ := h_ne
  -- Reindex meager sequences: (hm e) gives Sn_e with basin ⊆ ⋃_n Sn_e n.
  -- Combine via Nat.pair: S_k = Sn_e n where (e,n) = unpair k.
  let Sn (k : ℕ) : Set (ℕ → ℕ) :=
    let (e, n) := Nat.unpair k
    (Classical.choose (hm e)) n
  have hSn : ∀ k, NowhereDenseInFiber aps d (Sn k) := by
    intro k
    rw [show Sn k = (Classical.choose (hm ((Nat.unpair k).1))) ((Nat.unpair k).2) from rfl]
    exact (Classical.choose_spec (hm ((Nat.unpair k).1))).2 ((Nat.unpair k).2)
  obtain ⟨h, h_in, h_avoid⟩ := baire_category_fiber aps d h₀ h₀_in Sn hSn
  refine ⟨h, h_in, fun e => ?_⟩
  let Sn_e := Classical.choose (hm e)
  have h_sub : FixedPointBasin aps e d ⊆ ⋃ n, Sn_e n := (Classical.choose_spec (hm e)).1
  by_contra he_in
  have : h ∈ ⋃ n, Sn_e n := h_sub he_in
  obtain ⟨idx, hidx⟩ := Set.mem_iUnion.1 this
  have heq : Sn (Nat.pair e idx) = Sn_e idx := by
    simp only [Sn]
    rw [Nat.unpair_pair e idx]
  exact h_avoid (Nat.pair e idx) (heq.symm ▸ hidx)

end APSUniformization
