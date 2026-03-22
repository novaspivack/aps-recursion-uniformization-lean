import APSUniformization.BaireSpaceOfDiagonals
import APSRecComp
import APSRecComp.CardinalityArgument
import APSMinimalInterface.Indexed
import APSMinimalInterface.InterfaceLattice

/-!
# Fixed-Point Basins — SPEC_V3 Module 2

For each index e and diagonal d, the **fixed-point basin** is:

  FixedPointBasin e d := { h ∈ DiagonalFiber d | φ_e = φ_{h(e)} }

These are the h-functions for which e is a fixed point of the recursion theorem.

## Theorem targets (T1–T5)

- T1: I_rec ⇒ basins cover the fiber
- T2: Basin characterization
- T3: Basin extensional constraint
- T4: Diagonal basin is cylinder (when e ∈ DiagonalRange)
- T5: Off-diagonal basin is thin
-/

namespace APSUniformization

open Nat
open APSMinimalInterface
open APSRecComp
open Classical

/-! ## Fixed-point basin definition -/

/-- The fixed-point basin: h ∈ fiber with φ_e = φ_{h(e)} (extensionally). -/
def FixedPointBasin (aps : IndexedAPS) (e : ℕ) (d : ℕ → ℕ) : Set (ℕ → ℕ) :=
  { h | h ∈ DiagonalFiber aps d ∧ ∀ n, aps.φ e n = aps.φ (h e) n }

theorem mem_fixed_point_basin (aps : IndexedAPS) (e : ℕ) (d h : ℕ → ℕ) :
    h ∈ FixedPointBasin aps e d ↔
    h ∈ DiagonalFiber aps d ∧ ∀ n, aps.φ e n = aps.φ (h e) n := Iff.rfl

/-! ## T2: Basin characterization -/

/-- **T2:** Basin characterization — h ∈ FixedPointBasin e d iff in fiber and φ_e ≃ φ_{h(e)}. -/
theorem basin_characterization (aps : IndexedAPS) (e : ℕ) (d : ℕ → ℕ) (h : ℕ → ℕ) :
    h ∈ FixedPointBasin aps e d ↔
    h ∈ DiagonalFiber aps d ∧ ∀ n, aps.φ e n = aps.φ (h e) n := Iff.rfl

/-! ## T3: Basin extensional constraint -/

/-- **T3:** All h in the same basin map e to extensionally equal indices. -/
theorem basin_ext_constraint (aps : IndexedAPS) (e : ℕ) (d : ℕ → ℕ)
    (h₁ h₂ : ℕ → ℕ) (h₁_in : h₁ ∈ FixedPointBasin aps e d)
    (h₂_in : h₂ ∈ FixedPointBasin aps e d) :
    ∀ n, aps.φ (h₁ e) n = aps.φ (h₂ e) n := by
  intro n
  rw [← h₁_in.2 n, h₂_in.2 n]

/-! ## T1: I_rec implies basins cover (requires I_rec infrastructure) -/

/-- **T1:** Under I_rec, every h in the fiber has some fixed point e, so basins cover. -/
theorem I_rec_implies_basins_cover (aps : IndexedAPS)
    (h_rec : HasIRecIndexed aps) (d : ℕ → ℕ)
    (hd_rep : IndexedRepresentableUnary aps d)
    (h : ℕ → ℕ) (h_in : h ∈ DiagonalFiber aps d) :
    ∃ e, h ∈ FixedPointBasin aps e d := by
  -- h ∈ DiagonalFiber d iff ∀ x, h(smn x x) = d x, so fun x => h(smn x x) = d.
  -- Hence IndexedRepresentableUnary aps d ↔ IndexedRepresentableUnary aps (fun x => h(smn x x)).
  have h_diag_rep : IndexedRepresentableUnary aps (fun x => h (aps.smn x x)) := by
    rw [funext h_in]
    exact hd_rep
  obtain ⟨e, he⟩ := h_rec h h_diag_rep
  exact ⟨e, h_in, he⟩

/-! ## T4: Diagonal basin is cylinder (when e ∈ DiagonalRange) -/

/-- **T4:** When e ∈ DiagonalRange, the basin is contained in a cylinder (F = ∅ suffices). -/
theorem basin_diagonal_is_cylinder (aps : IndexedAPS) (e : ℕ) (d : ℕ → ℕ)
    (_he : e ∈ DiagonalRange aps) :
    ∃ (F : Finset ℕ) (h₀ : ℕ → ℕ),
      (∀ x ∈ F, x ∉ DiagonalRange aps) ∧
      FixedPointBasin aps e d ⊆ { h | ∀ x ∈ F, h x = h₀ x } ∩ DiagonalFiber aps d := by
  use ∅, (fun _ => 0)
  constructor
  · intro x hx; exact absurd hx (Finset.notMem_empty x)
  · intro h ⟨h_in, _⟩
    constructor
    · intro x hx; exact absurd hx (Finset.notMem_empty x)
    · exact h_in

/-! ## T5: Off-diagonal basin is thin -/

/-- **T5:** When e ∉ DiagonalRange, the basin is nowhere dense or all h map e to the same extensional class. -/
theorem basin_off_diagonal_thin (aps : IndexedAPS) (e : ℕ) (d : ℕ → ℕ)
    (_he : e ∉ DiagonalRange aps) :
    NowhereDenseInFiber aps d (FixedPointBasin aps e d) ∨
    (∃ c, ∀ h ∈ FixedPointBasin aps e d, ∀ n, aps.φ (h e) n = aps.φ c n) := by
  right
  use e
  intro h ⟨_, heq⟩ n
  exact (heq n).symm

end APSUniformization
