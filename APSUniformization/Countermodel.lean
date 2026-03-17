import Mathlib.Data.Part
import Mathlib.Data.Nat.Pairing
import APSMinimalInterface.Indexed
import APSMinimalInterface.IndexedCountermodels
import APSMinimalInterface.IndexedExactness

/-!
# Option B: Countermodel Attempt — FAILED

## Status: FAILED — extMinimalAPS does NOT have I_rec

**Critical finding:** extMinimalAPS does NOT satisfy I_rec (IndexedHasRecursionTheorem).

**Counterexample to I_rec:** Define h(x) = if x ∈ {2,6} then 3 else 2.
- h(smn x x) = 2 for all x (since smn x x ∉ {2,6}). So h_smn_rep holds with e₀=5.
- But no fixed point exists: for e ∈ range(smn), h(e)=2 and φ_2=fst≠φ_e (constant).
  For e=2: h(2)=3, φ_2=fst, φ_3=const 0. Not equal.
  For e=6: h(6)=3, φ_6=fst, φ_3=const 0. Not equal.

**Root cause:** smn(6,6) = extMinimalConstIndex 6 = 10 (not 6).
So h_no_fp(6) = 2 and φ_6 = φ_2 = fst — this IS a fixed point for h_no_fp specifically.
But for h that maps BOTH 2 and 6 away from {2,6}, no fixed point exists.

**Conclusion:** The separation was later proved with sepAPS (Separation.lean).
This file is kept for reference but NOT imported. The sorry below is irrelevant:
the theorem claim is false, and this file does not affect the build.

## What was attempted

Extend minimalIndexedAPS: add index 6 with φ_6 = first projection (fixed point for h_no_fp).
Add indices 7, 8 so smn(6,3)=7, smn(6,4)=8 avoid conflict with φ_6.
-/

namespace APSUniformization

open Nat
open APSMinimalInterface

/-! ## Extended minimal APS -/

/-- φ: 0,1,2 as minimal; 6 = first projection; 7 = const 3; 8 = const 4;
    9 = const 5; e'+10 = const (e'+6) for e'≥0. -/
def extMinimalφ (e n : ℕ) : Part ℕ :=
  match e with
  | 0 => Part.some 0
  | 1 => Part.some 1
  | 2 => Part.some (unpair n).1
  | 6 => Part.some (unpair n).1
  | 7 => Part.some 3
  | 8 => Part.some 4
  | 9 => Part.some 5
  | e'+10 => Part.some (e' + 6)
  | e'+3 => Part.some e'  -- 3,4,5 for const 0,1,2; 10,11,... match e'+10 first

/-- Index for const c: 0→3, 1→4, 2→5, 3→7, 4→8, 5+c'→9+c'. -/
def extMinimalConstIndex (c : ℕ) : ℕ :=
  match c with
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 7
  | 4 => 8
  | c'+5 => 9 + c'

/-- smn: 2 and 6 both use constIndex x (avoids 3+x hitting reserved 6,7,8,9); 9 and m+10 stay fixed. -/
def extMinimalSmn (e x : ℕ) : ℕ :=
  match e with
  | 0 => 0
  | 1 => 1
  | 2 => extMinimalConstIndex x
  | 6 => extMinimalConstIndex x
  | m+10 => m + 10
  | m+3 => m + 3

theorem extMinimal_φ_constIndex (c n : ℕ) :
    extMinimalφ (extMinimalConstIndex c) n = Part.some c := by
  match c with
  | 0 => simp [extMinimalConstIndex, extMinimalφ]
  | 1 => simp [extMinimalConstIndex, extMinimalφ]
  | 2 => simp [extMinimalConstIndex, extMinimalφ]
  | 3 => simp [extMinimalConstIndex, extMinimalφ]
  | 4 => simp [extMinimalConstIndex, extMinimalφ]
  | c + 5 =>
    simp only [extMinimalConstIndex]
    match c with
    | 0 => simp [extMinimalφ]
    | c + 1 =>
      show extMinimalφ (9 + (c + 1)) n = Part.some (c + 1 + 5)
      have h : 9 + (c + 1) = c + 10 := by omega
      have h2 : c + 1 + 5 = c + 6 := by omega
      rw [h, h2]
      simp [extMinimalφ]

theorem extMinimal_smn_spec (e x n : ℕ) :
    extMinimalφ (extMinimalSmn e x) n = extMinimalφ e (pair x n) := by
  match e with
  | 0 => rfl
  | 1 => rfl
  | 2 =>
    show extMinimalφ (extMinimalConstIndex x) n = extMinimalφ 2 (pair x n)
    rw [extMinimal_φ_constIndex x n]
    simp [extMinimalφ, unpair_pair]
  | 3 => simp [extMinimalφ, extMinimalSmn]
  | 4 => simp [extMinimalφ, extMinimalSmn]
  | 5 => simp [extMinimalφ, extMinimalSmn]
  | 6 =>
    show extMinimalφ (extMinimalConstIndex x) n = extMinimalφ 6 (pair x n)
    rw [extMinimal_φ_constIndex x n]
    simp [extMinimalφ, unpair_pair]
  | 7 => simp [extMinimalφ, extMinimalSmn]
  | 8 => simp [extMinimalφ, extMinimalSmn]
  | 9 => simp [extMinimalφ, extMinimalSmn]
  | e + 10 => simp [extMinimalφ, extMinimalSmn]

def extMinimalAPS : IndexedAPS where
  φ := extMinimalφ
  smn := extMinimalSmn
  smn_spec := extMinimal_smn_spec

/-! ## Representability -/

theorem extMinimal_rep_const (c : ℕ) :
    IndexedRepresentableUnary extMinimalAPS (fun _ => c) :=
  ⟨extMinimalConstIndex c, extMinimal_φ_constIndex c⟩

theorem extMinimal_rep_fst :
    IndexedRepresentableUnary extMinimalAPS (fun n => (unpair n).1) := by
  refine ⟨2, fun n => ?_⟩
  simp [extMinimalAPS, extMinimalφ]

/-! ## Nontriviality (advisor checklist) -/

/-- Nontrivial at n: at least two indices disagree at n. -/
def NontrivialAt (aps : IndexedAPS) (n : ℕ) : Prop :=
  ∃ a b, aps.φ a n ≠ aps.φ b n

theorem extMinimal_has_nontriviality : ∃ n, NontrivialAt extMinimalAPS n := by
  refine ⟨0, 0, 1, fun h => Nat.zero_ne_one (Part.some_inj.mp h)⟩

/-! ## h_no_fp has fixed point (e=6) -/

theorem extMinimal_smn_xx_ne_two (x : ℕ) : extMinimalSmn x x ≠ 2 := by
  match x with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | x + 3 =>
    -- Case x+3: extMinimalSmn (x+3)(x+3) matches m+3 branch when x+3≥7, else 6 branch.
    -- For x=3: extMinimalSmn 6 6 = extMinimalConstIndex 6 = 10 ≠ 2.
    -- For x≠3: extMinimalSmn (x+3)(x+3) = x+3 ≥ 3 ≠ 2.
    match x with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide  -- extMinimalSmn 6 6 = 10 ≠ 2
    | 4 => decide
    | 5 => decide
    | 6 => decide
    | x + 7 =>
      simp only [extMinimalSmn]
      omega

theorem extMinimal_h_no_fp_smn (x : ℕ) :
    minimalIndexed_h_no_fp (extMinimalSmn x x) = 2 := by
  simp only [minimalIndexed_h_no_fp, extMinimal_smn_xx_ne_two, ite_false]

theorem extMinimal_rep_h_no_fp_smn :
    IndexedRepresentableUnary extMinimalAPS (fun x => minimalIndexed_h_no_fp (extMinimalAPS.smn x x)) := by
  refine ⟨5, fun n => ?_⟩
  simp only [extMinimalAPS, extMinimalφ, extMinimal_h_no_fp_smn]

theorem extMinimal_h_no_fp_fixed_point :
    ∃ e, ∀ n, extMinimalAPS.φ e n = extMinimalAPS.φ (minimalIndexed_h_no_fp e) n := by
  refine ⟨6, fun n => ?_⟩
  -- φ_6 n = (unpair n).1; h_no_fp 6 = 2 (since 6 ≠ 2); φ_2 n = (unpair n).1
  have : minimalIndexed_h_no_fp 6 = 2 := by simp [minimalIndexed_h_no_fp]
  simp only [extMinimalAPS, extMinimalφ, this]

/-! ## I_rec for extended APS -/

/-- For e ∈ {0,1,3,4,5,7,8,9} or e≥10, extMinimalφ e is constant. -/
theorem extMinimal_φ_is_const_of_e (e : ℕ) (h2 : e ≠ 2) (h6 : e ≠ 6) :
    ∃ c, ∀ n, extMinimalφ e n = Part.some c := by
  match e with
  | 0 => exact ⟨0, fun _ => rfl⟩
  | 1 => exact ⟨1, fun _ => rfl⟩
  | 2 => exact absurd rfl h2
  | 3 => exact ⟨0, fun _ => rfl⟩
  | 4 => exact ⟨1, fun _ => rfl⟩
  | 5 => exact ⟨2, fun _ => rfl⟩
  | 6 => exact absurd rfl h6
  | 7 => exact ⟨3, fun _ => rfl⟩
  | 8 => exact ⟨4, fun _ => rfl⟩
  | 9 => exact ⟨5, fun _ => rfl⟩
  | e + 10 => exact ⟨e + 6, fun _ => rfl⟩

/-- extMinimalSmn x x is never 2 or 6 (so h(smn x x) is always constant). -/
theorem extMinimal_smn_xx_ne_six (x : ℕ) : extMinimalSmn x x ≠ 6 := by
  match x with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | 5 => decide
  | 6 => decide
  | x + 7 =>
    -- extMinimalSmn (x+7)(x+7) = x+7 via m+3 branch; x+7 ≥ 7 > 6.
    match x with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | x + 4 =>
      simp only [extMinimalSmn]
      omega

/-- **Failure analysis (this theorem is false):** extMinimalAPS does NOT satisfy I_rec.
    Counterexample: h(x) = if x ∈ {2,6} then 3 else 2. Then h(smn x x) = 2 for all x (witness e₀=5),
    but no fixed point exists: for e ∈ range(smn), h(e)=2 and φ_e is constant while φ_2 is fst;
    for e ∈ {2,6}, h(e)=3 and φ_3 = const 0 ≠ φ_2, φ_6. Root cause: smn(6,6)=10, so indices 2,6
    have no representative outside range(smn); h mapping both to const indices has no fixed point.
    This file is NOT imported. See FINAL_STATUS_AND_HANDOFF.md §9. -/
theorem extMinimal_has_I_rec_INCORRECT_CLAIM : HasIRecIndexed extMinimalAPS := by
  intro h h_smn_rep
  obtain ⟨e₀, he₀⟩ := h_smn_rep
  -- Determine c = h(smn 0 0) = h(0)
  by_cases he2 : e₀ = 2 ∨ e₀ = 6
  · -- Case e₀ ∈ {2,6}: φ e₀ = first projection; from he₀ 0, h(0) = (unpair 0).1 = 0.
    have hsmn00 : extMinimalAPS.smn 0 0 = 0 := by simp [extMinimalAPS, extMinimalSmn]
    have hh0 : h 0 = 0 := by
      have key := he₀ 0
      simp only [extMinimalAPS, hsmn00] at key
      cases he2 with
      | inl h2 =>
        rw [h2] at key
        simp only [extMinimalφ] at key
        exact Part.some_inj.mp key.symm
      | inr h6 =>
        rw [h6] at key
        simp only [extMinimalφ] at key
        exact Part.some_inj.mp key.symm
    exact ⟨0, fun n => by simp only [extMinimalAPS, extMinimalφ, hh0]⟩
  · -- Case e₀ ∉ {2,6}: φ e₀ is constant; h(smn x x) = h(smn 0 0) for all x.
    push_neg at he2
    obtain ⟨hne2, hne6⟩ := he2
    have hφ_const : ∀ n m, extMinimalAPS.φ e₀ n = extMinimalAPS.φ e₀ m := by
      intro n m
      obtain ⟨c, hc⟩ := extMinimal_φ_is_const_of_e e₀ hne2 hne6
      simp only [extMinimalAPS] at hc ⊢
      rw [hc n, hc m]
    have hc : ∀ x, h (extMinimalAPS.smn x x) = h (extMinimalAPS.smn 0 0) := by
      intro x
      have h1 : extMinimalAPS.φ e₀ 0 = Part.some (h (extMinimalAPS.smn 0 0)) := he₀ 0
      have h2 : extMinimalAPS.φ e₀ x = Part.some (h (extMinimalAPS.smn x x)) := he₀ x
      have heq : extMinimalAPS.φ e₀ x = extMinimalAPS.φ e₀ 0 := hφ_const x 0
      exact Part.some_inj.mp (h2.symm.trans (heq.trans h1))
    have hsmn00 : extMinimalAPS.smn 0 0 = 0 := by simp [extMinimalAPS, extMinimalSmn]
    have hconst : ∀ x, h (extMinimalAPS.smn x x) = h 0 := by
      intro x
      have := hc x
      rw [hsmn00] at this
      exact this
    by_cases hc2 : h 0 = 2
    · -- Subcase h(0)=2: no fixed point exists (counterexample h(2)=h(6)=3).
      exact absurd rfl (by omega)
    · -- Subcase h(0)≠2: would use e = extMinimalConstIndex (h 0); fails when h(0)=6.
      -- IRRELEVANT: theorem claim is false; file not imported; does not affect build.
      sorry

/-! ## ¬I_comp: first projection has no tracker -/

theorem extMinimal_no_comp : ¬ HasICompIndexed extMinimalAPS := by
  intro ⟨inst⟩
  have h := inst.comp (fun x => (unpair x).1) extMinimal_rep_fst
  obtain ⟨k, hk⟩ := h
  have h_pair := hk (pair 0 1) 0
  have h_one := hk 2 0
  simp only [extMinimalφ, extMinimalAPS, unpair_pair] at h_pair h_one
  have h2 : (unpair 2).1 = 1 := by have : 2 = pair 1 0 := rfl; rw [this, unpair_pair]
  rw [h2] at h_one
  cases k with
  | zero => exact Nat.zero_ne_one (Part.some_inj.mp h_one)
  | succ k =>
    cases k with
    | zero => exact Nat.one_ne_zero (Part.some_inj.mp h_pair)
    | succ k =>
      cases k with
      | zero =>
        simp only [extMinimalφ, extMinimalSmn] at h_one
        exact Nat.zero_ne_one (Part.some_inj.mp h_one)
      | succ k =>
        cases k with
        | zero =>
          simp only [extMinimalφ, extMinimalSmn] at h_one
          exact Nat.zero_ne_one (Part.some_inj.mp h_one)
        | succ k =>
          cases k with
          | zero =>
            simp only [extMinimalφ, extMinimalSmn] at h_one
            exact Nat.zero_ne_one (Part.some_inj.mp h_one)
          | succ k =>
            have heq := Part.some_inj.mp h_pair
            omega

/-! ## Main results -/

-- I_rec_not_implies_I_comp cannot be proved with extMinimalAPS: the construction
-- does not satisfy I_rec. The separation was later proved with sepAPS (Separation.lean).
-- This theorem is commented out; the file is not imported.
-- theorem I_rec_not_implies_I_comp :
--     ∃ aps : IndexedAPS, HasIRecIndexed aps ∧ ¬ HasICompIndexed aps :=
--   ⟨extMinimalAPS, extMinimal_has_I_rec_INCORRECT_CLAIM, extMinimal_no_comp⟩

end APSUniformization
