import APSRecComp
import APSRecComp.CardinalityArgument
import APSRecComp.SmnSectionSurjectivity
import APSRecComp.FiniteTracking
import APSRecComp.ConditionalNecessity
import APSMinimalInterface.Indexed
import APSMinimalInterface.InterfaceLattice
import Mathlib.Data.Finset.Basic

/-!
# Baire Space of Diagonals — SPEC_V3 Module 1

## The function space setup

Fix a representable diagonal d : ℕ → ℕ. The **diagonal fiber** is:

  DiagonalFiber d := { h : ℕ → ℕ | ∀ x, h(smn x x) = d x }

This is the space of all h-functions qualifying for I_rec with diagonal d.
h is constrained on DiagonalRange = {smn(x,x) | x ∈ ℕ} and free elsewhere.

We formalize a combinatorial version of the Baire category theorem:
a countable union of "nowhere dense" sets cannot cover the fiber.

## Key theorems

- T0: The fiber is nonempty and has full off-diagonal freedom
- T0': Combinatorial Baire: countable union of nowhere dense sets ≠ fiber
-/

namespace APSUniformization

open Nat
open APSMinimalInterface
open APSRecComp
open Classical

/-! ## Diagonal fiber -/

/-- The diagonal fiber: all h with h(smn x x) = d x for all x. -/
def DiagonalFiber (aps : IndexedAPS) (d : ℕ → ℕ) : Set (ℕ → ℕ) :=
  { h | ∀ x, h (aps.smn x x) = d x }

theorem mem_diagonal_fiber (aps : IndexedAPS) (d h : ℕ → ℕ) :
    h ∈ DiagonalFiber aps d ↔ ∀ x, h (aps.smn x x) = d x := Iff.rfl

/-- The constant-d function (extended by d off-diagonal) is in the fiber. -/
def canonicalFiberElement (_aps : IndexedAPS) (d : ℕ → ℕ) : ℕ → ℕ :=
  fun _ => d 0

theorem canonical_in_fiber (aps : IndexedAPS) (d : ℕ → ℕ)
    (h_const : ∀ x, d x = d 0) : canonicalFiberElement aps d ∈ DiagonalFiber aps d := by
  intro x; simp [canonicalFiberElement, h_const x]

/-- When d is constant, the fiber is nonempty (canonical element). -/
theorem diagonal_fiber_nonempty_of_const (aps : IndexedAPS) (d : ℕ → ℕ)
    (h_const : ∀ x, d x = d 0) : (DiagonalFiber aps d).Nonempty :=
  ⟨canonicalFiberElement aps d, canonical_in_fiber aps d h_const⟩

/-- The fiber is nonempty when d is constant. For general d, the fiber may be empty
    (it requires d to be smn-diagonal-consistent). -/
theorem diagonal_fiber_nonempty (aps : IndexedAPS) (d : ℕ → ℕ)
    (h_const : ∀ x, d x = d 0) : (DiagonalFiber aps d).Nonempty :=
  diagonal_fiber_nonempty_of_const aps d h_const

/-- When d is smn-diagonal-consistent (d(x₁)=d(x₂) whenever smn(x₁,x₁)=smn(x₂,x₂)),
    the fiber is nonempty. Construction: h(y) = d(x) for x with smn(x,x)=y when y ∈ DiagonalRange. -/
theorem diagonal_fiber_nonempty_of_smn_consistent (aps : IndexedAPS) (d : ℕ → ℕ)
    (h_smn_inj : ∀ x₁ x₂, aps.smn x₁ x₁ = aps.smn x₂ x₂ → d x₁ = d x₂) :
    (DiagonalFiber aps d).Nonempty := by
  let diag := fun (x : ℕ) => aps.smn x x
  let h (y : ℕ) : ℕ :=
    if hy : y ∈ Set.range diag then d (Classical.choose (Set.mem_range.mp hy))
    else d 0
  refine ⟨h, fun x => ?_⟩
  simp only [h]
  have hx : aps.smn x x ∈ Set.range diag := ⟨x, rfl⟩
  rw [dif_pos hx]
  let z := Classical.choose (Set.mem_range.mp hx)
  have heq_diag : diag z = diag x := Classical.choose_spec (Set.mem_range.mp hx)
  have heq : aps.smn z z = aps.smn x x := by simp only [diag] at heq_diag; exact heq_diag
  exact h_smn_inj z x heq

/-- For representable d, the fiber is nonempty when smn is injective on the diagonal. -/
theorem diagonal_fiber_nonempty_of_rep (aps : IndexedAPS) (d : ℕ → ℕ)
    (_hd : IndexedRepresentableUnary aps d)
    (h_smn_inj : Function.Injective (fun x => aps.smn x x)) :
    (DiagonalFiber aps d).Nonempty := by
  have h_consist : ∀ x₁ x₂, aps.smn x₁ x₁ = aps.smn x₂ x₂ → d x₁ = d x₂ :=
    fun x₁ x₂ heq => congr_arg d (h_smn_inj heq)
  exact diagonal_fiber_nonempty_of_smn_consistent aps d h_consist

/-! ## Off-diagonal freedom -/

/-- For any off-diagonal point y and value c, there exists h in the fiber with h(y) = c. -/
theorem fiber_off_diagonal_free (aps : IndexedAPS) (d : ℕ → ℕ)
    (h₀ : ℕ → ℕ) (h₀_in : h₀ ∈ DiagonalFiber aps d)
    (y : ℕ) (hy : y ∉ DiagonalRange aps) (c : ℕ) :
    ∃ h ∈ DiagonalFiber aps d, h y = c ∧ ∀ z ≠ y, h z = h₀ z := by
  refine ⟨fun z => if z = y then c else h₀ z, ?_, ?_, ?_⟩
  · intro x
    have hne : aps.smn x x ≠ y := fun heq => hy ⟨x, heq⟩
    simp [hne, h₀_in x]
  · simp
  · intro z hz; simp [hz]

/-- For any finite set of off-diagonal indices and values, there exists h in the fiber
    with those values. -/
theorem fiber_finite_freedom (aps : IndexedAPS) (d : ℕ → ℕ)
    (h₀ : ℕ → ℕ) (h₀_in : h₀ ∈ DiagonalFiber aps d)
    (F : Finset ℕ) (hF : ∀ x ∈ F, x ∉ DiagonalRange aps)
    (vals : ℕ → ℕ) :
    ∃ h ∈ DiagonalFiber aps d, ∀ x ∈ F, h x = vals x := by
  refine ⟨fun z => if z ∈ F then vals z else h₀ z, ?_, ?_⟩
  · intro x
    have hne : aps.smn x x ∉ F := fun hxF => hF _ hxF ⟨x, rfl⟩
    simp [hne, h₀_in x]
  · intro x hx; simp [hx]

/-! ## Nowhere dense sets -/

/-- A set S is nowhere dense in the fiber: every finite cylinder can be refined
    to avoid S. -/
def NowhereDenseInFiber (aps : IndexedAPS) (d : ℕ → ℕ) (S : Set (ℕ → ℕ)) : Prop :=
  ∀ (h₀ : ℕ → ℕ) (F : Finset ℕ),
    h₀ ∈ DiagonalFiber aps d →
    (∀ x ∈ F, x ∉ DiagonalRange aps) →
    ∃ (h₁ : ℕ → ℕ) (G : Finset ℕ),
      h₁ ∈ DiagonalFiber aps d ∧
      F ⊆ G ∧
      (∀ x ∈ F, h₁ x = h₀ x) ∧
      (∀ x ∈ G, x ∉ DiagonalRange aps) ∧
      (∀ h ∈ DiagonalFiber aps d, (∀ x ∈ G, h x = h₁ x) → h ∉ S)

/-- A set is meager if it is a countable union of nowhere dense sets. -/
def MeagerInFiber (aps : IndexedAPS) (d : ℕ → ℕ) (S : Set (ℕ → ℕ)) : Prop :=
  ∃ (Sn : ℕ → Set (ℕ → ℕ)),
    S ⊆ ⋃ n, Sn n ∧
    ∀ n, NowhereDenseInFiber aps d (Sn n)

/-- The empty set is nowhere dense. -/
theorem empty_nowhere_dense (aps : IndexedAPS) (d : ℕ → ℕ) :
    NowhereDenseInFiber aps d ∅ := by
  intro h₀ F h₀_in hF
  exact ⟨h₀, F, h₀_in, Finset.Subset.refl F, fun _ _ => rfl, hF, fun _ _ _ h => h⟩

/-- Subsets of nowhere dense sets are nowhere dense. -/
theorem nowhere_dense_mono (aps : IndexedAPS) (d : ℕ → ℕ) (S T : Set (ℕ → ℕ))
    (hST : S ⊆ T) (hT : NowhereDenseInFiber aps d T) :
    NowhereDenseInFiber aps d S := by
  intro h₀ F h₀_in hF
  obtain ⟨h₁, G, h₁_in, hFG, h_agree, hGoff, hcyl⟩ := hT h₀ F h₀_in hF
  exact ⟨h₁, G, h₁_in, hFG, h_agree, hGoff, fun h h_in hagreees hmem =>
    absurd (hST hmem) (hcyl h h_in hagreees)⟩

/-! ## Baire sequence construction -/

/-- One step of the Baire diagonalization: given (h_n, G_n), produce (h_{n+1}, G_{n+1})
    that avoids S_n. Uses Classical.choice to extract from the nowhere-dense witness. -/
noncomputable def baireStep (aps : IndexedAPS) (d : ℕ → ℕ) (Sn : ℕ → Set (ℕ → ℕ))
    (hSn : ∀ n, NowhereDenseInFiber aps d (Sn n))
    (n : ℕ) (h_n : ℕ → ℕ) (G_n : Finset ℕ)
    (h_n_in : h_n ∈ DiagonalFiber aps d)
    (hGoff : ∀ x ∈ G_n, x ∉ DiagonalRange aps) : (ℕ → ℕ) × Finset ℕ :=
  let r := hSn n h_n G_n h_n_in hGoff
  (Classical.choose r, (Classical.choose_spec r).choose)

/-- **Combinatorial Baire theorem (T0'):**
    A countable union of nowhere dense sets does not cover the diagonal fiber.

    Proof sketch: Build h* by diagonalization. At step n, we have a "commitment"
    (h_n, G_n) where h_n ∈ fiber and G_n is a finite set of off-diagonal indices
    on which h* is already determined. Use nowhere-denseness of S_n to extend
    (h_n, G_n) to (h_{n+1}, G_{n+1}) with G_n ⊆ G_{n+1}, h_{n+1} agrees with h_n
    on G_n, and no h agreeing with h_{n+1} on G_{n+1} is in S_n.
    Define h*(y) = h_n(y) for the first n with y ∈ G_n, and d(0) otherwise.
    Then h* ∈ fiber and h* ∉ S_n for all n.

    The Lean proof uses Classical.choice to build the sequence. -/
theorem baire_category_fiber (aps : IndexedAPS) (d : ℕ → ℕ)
    (h₀ : ℕ → ℕ) (h₀_in : h₀ ∈ DiagonalFiber aps d)
    (Sn : ℕ → Set (ℕ → ℕ))
    (hSn : ∀ n, NowhereDenseInFiber aps d (Sn n)) :
    ∃ h ∈ DiagonalFiber aps d, ∀ n, h ∉ Sn n := by
  -- Baire construction: build (h_n, G_n) with G_n ⊆ G_{n+1} and h_{n+1} agreeing with h_n on G_n.
  -- At step n, baireStep produces (h_{n+1}, G_{n+1}) such that any h agreeing with h_{n+1}
  -- on G_{n+1} avoids S_n. Define h*(x) = h_k(x) for the least k with x ∈ G_k; for x ∉ ⋃ G_n
  -- use h₀(x). Monotonicity and agreement ensure h* ∉ S_n for all n.
  let seq : ℕ → Σ' (h : ℕ → ℕ) (G : Finset ℕ),
      h ∈ DiagonalFiber aps d ∧ (∀ x ∈ G, x ∉ DiagonalRange aps) :=
    Nat.rec ⟨h₀, ∅, h₀_in, fun x hx => absurd hx (Finset.notMem_empty x)⟩
      (fun n prev =>
        let p := baireStep aps d Sn hSn n prev.1 prev.2.1 prev.2.2.1 prev.2.2.2
        let hp := (Classical.choose_spec (hSn n prev.1 prev.2.1 prev.2.2.1 prev.2.2.2)).choose_spec
        ⟨p.1, p.2, hp.1, hp.2.2.2.1⟩)
  -- Structural facts: G_m ⊆ G_{m+1} and h_{m+1} agrees with h_m on G_m
  have seq_G_mono : ∀ m, (seq m).2.1 ⊆ (seq (m + 1)).2.1 := by
    intro m; unfold seq; simp only
    exact (Classical.choose_spec (hSn m (seq m).1 (seq m).2.1 (seq m).2.2.1 (seq m).2.2.2)).choose_spec.2.1
  have seq_agree : ∀ m x, x ∈ (seq m).2.1 → (seq (m + 1)).1 x = (seq m).1 x := by
    intro m x hx; unfold seq; simp only
    exact (Classical.choose_spec (hSn m (seq m).1 (seq m).2.1 (seq m).2.2.1 (seq m).2.2.2)).choose_spec.2.2.1 x hx
  -- Transitivity: G_i ⊆ G_j for i ≤ j
  -- Transitivity: G_i ⊆ G_j for i ≤ j
  have seq_G_mono_trans : ∀ i j, i ≤ j → (seq i).2.1 ⊆ (seq j).2.1 := by
    intro i j hij
    induction j with
    | zero =>
      have hi : i = 0 := Nat.eq_zero_of_le_zero hij
      subst hi
      rfl
    | succ j ih =>
      by_cases hij' : i ≤ j
      · exact Finset.Subset.trans (ih hij') (seq_G_mono j)
      · have hlt : j < i := (Nat.lt_or_ge j i).elim id (fun h => absurd h hij')
        have hi : i = j + 1 := Nat.le_antisymm hij (Nat.succ_le_of_lt hlt)
        subst hi
        rfl
  -- For i ≤ j and x ∈ G_{i+1}, h_{j+1}(x) = h_{i+1}(x)
  have seq_agree_trans : ∀ i j, i ≤ j → ∀ x, x ∈ (seq (i + 1)).2.1 →
      (seq (j + 1)).1 x = (seq (i + 1)).1 x := by
    intro i j hij x hx
    induction j with
    | zero =>
      have hi : i = 0 := Nat.eq_zero_of_le_zero hij
      subst hi
      rfl
    | succ j ih =>
      by_cases hij' : i ≤ j
      · have hxG : x ∈ (seq (j + 1)).2.1 := (seq_G_mono_trans (i + 1) (j + 1) (Nat.succ_le_succ hij')) hx
        rw [seq_agree (j + 1) x hxG]
        exact ih hij'
      · have hlt : j < i := (Nat.lt_or_ge j i).elim id (fun h => absurd h hij')
        have hi : i = j + 1 := Nat.le_antisymm hij (Nat.succ_le_of_lt hlt)
        subst hi
        rfl
  -- Define h*: for y in some G_{k+1}, use (seq (k+1)).1 y; else h₀ y
  let hStar (y : ℕ) : ℕ :=
    if hex : ∃ k, y ∈ (seq (k + 1)).2.1
    then (seq (Classical.choose hex + 1)).1 y
    else h₀ y
  refine ⟨hStar, ?_, fun n => ?_⟩
  · intro x
    by_cases hex : ∃ k, aps.smn x x ∈ (seq (k + 1)).2.1
    · simp only [hStar, dif_pos hex]
      exact ((seq (Classical.choose hex + 1)).2.2.1) x
    · simp only [hStar, dif_neg hex]
      exact h₀_in x
  · let r := hSn n (seq n).1 (seq n).2.1 (seq n).2.2.1 (seq n).2.2.2
    have hcyl := r.choose_spec.choose_spec.2.2.2.2
    apply hcyl hStar
    · -- hStar ∈ DiagonalFiber
      intro x
      by_cases hex : ∃ k, aps.smn x x ∈ (seq (k + 1)).2.1
      · simp only [hStar, dif_pos hex]; exact ((seq (Classical.choose hex + 1)).2.2.1) x
      · simp only [hStar, dif_neg hex]; exact h₀_in x
    · -- ∀ x ∈ G_new, hStar x = h_new x  where G_new = r.choose_spec.choose, h_new = Classical.choose r
      intro x hxG
      simp only [hStar]
      have hex : ∃ k, x ∈ (seq (k + 1)).2.1 := ⟨n, by rw [show (seq (n + 1)).2.1 = r.choose_spec.choose from rfl]; exact hxG⟩
      simp only [dif_pos hex]
      have hseq_eq : (seq (n + 1)).1 = Classical.choose r ∧ (seq (n + 1)).2.1 = r.choose_spec.choose := by
        unfold seq; simp only; exact ⟨rfl, rfl⟩
      -- Sequence consistency: when x ∈ G_{k+1} and x ∈ G_{n+1}, h_{k+1}(x) = h_{n+1}(x)
      have hconsist : (seq (Classical.choose hex + 1)).1 x = (seq (n + 1)).1 x := by
        let k := Classical.choose hex
        have hxk : x ∈ (seq (k + 1)).2.1 := Classical.choose_spec hex
        by_cases hkn : k ≤ n
        · exact (seq_agree_trans k n (by omega) x hxk).symm
        · have hnk : n ≤ k := Nat.le_of_not_le hkn
          exact seq_agree_trans n k (by omega) x hxG
      rw [hconsist, hseq_eq.1]

/-- **Corollary:** If all basins are meager, the fiber is not covered. -/
theorem meager_union_not_cover (aps : IndexedAPS) (d : ℕ → ℕ)
    (h₀ : ℕ → ℕ) (h₀_in : h₀ ∈ DiagonalFiber aps d)
    (Sn : ℕ → Set (ℕ → ℕ))
    (hSn : ∀ n, NowhereDenseInFiber aps d (Sn n)) :
    ∃ h ∈ DiagonalFiber aps d, ∀ n, h ∉ Sn n :=
  baire_category_fiber aps d h₀ h₀_in Sn hSn

/-! ## Key structural lemma: off-diagonal modification -/

/-- Modifying h at a single off-diagonal point stays in the fiber. -/
theorem modify_off_diagonal (aps : IndexedAPS) (d : ℕ → ℕ)
    (h : ℕ → ℕ) (h_in : h ∈ DiagonalFiber aps d)
    (y : ℕ) (hy : y ∉ DiagonalRange aps) (c : ℕ) :
    (fun z => if z = y then c else h z) ∈ DiagonalFiber aps d := by
  intro x
  have hne : aps.smn x x ≠ y := fun heq => hy ⟨x, heq⟩
  simp [hne, h_in x]

/-- The fiber is "dense" in the off-diagonal directions:
    for any h in the fiber and any off-diagonal point y, every value c
    is realized by some h' in the fiber agreeing with h everywhere except y. -/
theorem fiber_dense_off_diagonal (aps : IndexedAPS) (d : ℕ → ℕ)
    (h : ℕ → ℕ) (h_in : h ∈ DiagonalFiber aps d)
    (y : ℕ) (hy : y ∉ DiagonalRange aps) (c : ℕ) :
    ∃ h' ∈ DiagonalFiber aps d, h' y = c ∧ ∀ z ≠ y, h' z = h z := by
  exact ⟨fun z => if z = y then c else h z,
    modify_off_diagonal aps d h h_in y hy c,
    by simp,
    fun z hz => by simp [hz]⟩

end APSUniformization
