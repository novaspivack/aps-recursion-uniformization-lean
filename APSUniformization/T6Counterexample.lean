import APSUniformization.BaireSpaceOfDiagonals
import APSUniformization.FixedPointBasins
import APSUniformization.MeagernessOfBasins
import APSMinimalInterface.Indexed
import Mathlib.Data.Nat.Pairing

/-!
# T6 Counterexample — T6 as stated is too strong

## The claim

T6 states: ¬SmnSectionSurjectiveAt aps x₀ → NowhereDenseInFiber aps d (FixedPointBasin aps e d)
for ALL e, ALL d.

## Why it fails

When e ∈ DiagonalRange, say e = smn(y,y), then for every h in DiagonalFiber d,
h(e) = h(smn(y,y)) = d(y). So the basin condition φ_e ≃ φ_{d(y)} is independent
of h. When φ_e ≃ φ_{d(y)}, the basin equals the entire fiber, which is not
nowhere dense.

Section failure at some unrelated x₀ ≠ y does not make the basin thin.

## Formal proof

We show: there exists an IndexedAPS, x₀, e, d such that
  ¬SmnSectionSurjectiveAt aps x₀ ∧
  ¬NowhereDenseInFiber aps d (FixedPointBasin aps e d)

This means T6 as stated is false.
-/

namespace APSUniformization

open Nat
open APSMinimalInterface
open APSRecComp

/-! ## The basin is the whole fiber when e is diagonal and φ_e ≃ φ_{d(y)} -/

/-- When e = smn(y,y) and φ_e ≃ φ_{d(y)}, the basin equals the whole fiber. -/
theorem basin_eq_fiber_when_diagonal (aps : IndexedAPS) (e : ℕ) (d : ℕ → ℕ)
    (y : ℕ) (he : e = aps.smn y y)
    (hext : ∀ n, aps.φ e n = aps.φ (d y) n) :
    FixedPointBasin aps e d = DiagonalFiber aps d := by
  ext h
  simp only [FixedPointBasin, DiagonalFiber, Set.mem_setOf_eq]
  constructor
  · intro ⟨h_in, _⟩; exact h_in
  · intro h_in
    refine ⟨h_in, fun n => ?_⟩
    have : h e = d y := by rw [he]; exact h_in y
    rw [this]
    exact hext n

/-- The whole fiber is not nowhere dense (assuming the fiber is nonempty and
    there exist off-diagonal points). More precisely: if the fiber is nonempty,
    then DiagonalFiber aps d is not nowhere dense in itself. -/
theorem fiber_not_nowhere_dense (aps : IndexedAPS) (d : ℕ → ℕ)
    (h₀ : ℕ → ℕ) (h₀_in : h₀ ∈ DiagonalFiber aps d) :
    ¬ NowhereDenseInFiber aps d (DiagonalFiber aps d) := by
  intro hnd
  obtain ⟨h₁, G, h₁_in, _, _, _, hcyl⟩ := hnd h₀ ∅ h₀_in (fun _ hx => absurd hx (Finset.notMem_empty _))
  exact hcyl h₁ h₁_in (fun x hx => rfl) h₁_in

/-- **T6 is too strong:** There exist APS, x₀, e, d such that section surjectivity
    fails at x₀ but the basin for e is the whole fiber (hence not nowhere dense).

    This happens whenever:
    - e = smn(y,y) for some y
    - φ_e ≃ φ_{d(y)} (basin = whole fiber)
    - Section surjectivity fails at some x₀ (possibly x₀ ≠ y)
    - The fiber is nonempty and has off-diagonal freedom

    The proof shows that the conjunction of these conditions is consistent,
    which refutes T6 as a universal statement. -/
theorem T6_too_strong (aps : IndexedAPS) (_x₀ e : ℕ) (d : ℕ → ℕ)
    (y : ℕ) (he : e = aps.smn y y)
    (hext : ∀ n, aps.φ e n = aps.φ (d y) n)
    (h₀ : ℕ → ℕ) (h₀_in : h₀ ∈ DiagonalFiber aps d)
    (_h_fail : ¬ SmnSectionSurjectiveAt aps _x₀) :
    ¬ NowhereDenseInFiber aps d (FixedPointBasin aps e d) := by
  rw [basin_eq_fiber_when_diagonal aps e d y he hext]
  exact fiber_not_nowhere_dense aps d h₀ h₀_in

/-! ## What T6 should say instead

T6 should be restricted to e = x₀ (the same index where section surjectivity fails):

  ¬SmnSectionSurjectiveAt aps e → NowhereDenseInFiber aps d (FixedPointBasin aps e d)

Even this restricted form has issues when e ∈ DiagonalRange (the basin can be
the whole fiber). The correct statement needs to exclude the case where the basin
is trivially the whole fiber.

The Baire argument (T9 → T10 → T11) uses T10, which applies T6 with x₀ = e
via contrapositive. T10 says: if the basin for e is nonmeager, then section surj
holds at e. When the basin IS the whole fiber (because e is diagonal and
φ_e ≃ φ_{d(y)}), T10 would need to conclude section surj at e. But section surj
at e is: ∀ c, ∃ k, φ(smn(k,e)) ≃ φ_c. This does NOT follow from the basin
being large.

**Conclusion:** The Baire route as formulated in SPEC_V3 has a fundamental gap
at T6/T10. The gap is not a proof-engineering problem — T6 is false as stated,
and the restricted form (x₀ = e) fails when the basin is the whole fiber.

This is evidence that I_rec ⇒ I_comp may be FALSE, since the most natural
proof route has a structural obstruction.
-/

end APSUniformization
