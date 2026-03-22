import APSMinimalInterface.Indexed
import APSUniformization.GValRealization
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Part

/-!
# Separation: I_rec ∧ ¬I_comp

An IndexedAPS where the recursion theorem holds but composition fails.

## The model

- φ_0 = ⊥ (totally undefined)
- φ_1 = g_val (non-constant total function with g_val(pair(1,n)) = g_val(n))
- φ_{c+2} = const_c

g_val strips leading 1s from the pair decomposition:
  g_val(pair(0,n)) = 0, g_val(pair(1,n)) = g_val(n), g_val(pair(c+2,n)) = c+2.

The self-sectioning property g_val(pair(1,n)) = g_val(n) ensures smn(1,1) = 1,
placing the non-constant index on the diagonal.

## smn

- smn(0, x) = 0
- smn(1, 0) = 2, smn(1, 1) = 1, smn(1, c+2) = c+2
- smn(c+2, x) = c+2

Diagonal: smn(x,x) = x for all x.

## Results

- I_rec holds: every representable h (= g_val or const_c) has a fixed point
- I_comp fails: g_val maps some inputs to ⊥-class and others to defined classes;
  no single index can track this mix
-/

namespace APSUniformization

open Nat
open APSMinimalInterface

/-! ## The function g_val (axiomatized)

g_val is a total function ℕ → ℕ satisfying:
  g_val(pair(0,n)) = 0
  g_val(pair(1,n)) = g_val(n)
  g_val(pair(c+2,n)) = c
  g_val(0) = 0

Such a function exists: define g_val(n) by recursion on n, stripping leading 1s
from the pair tree. The recursion terminates because (unpair n).2 < n when
(unpair n).1 ≥ 1. We axiomatize it here to avoid well-foundedness proof engineering. -/

def g_val : ℕ → ℕ := g_val_def

theorem g_val_pair_zero (n : ℕ) : g_val (Nat.pair 0 n) = 0 := g_val_def_pair_zero n
theorem g_val_pair_one (n : ℕ) : g_val (Nat.pair 1 n) = g_val n := g_val_def_pair_one n
theorem g_val_pair_succ_succ (c n : ℕ) : g_val (Nat.pair (c + 2) n) = c + 2 := g_val_def_pair_succ_succ c n
theorem g_val_zero : g_val 0 = 0 := g_val_def_zero

/-! ## The APS -/

noncomputable def sepφ (e n : ℕ) : Part ℕ :=
  match e with
  | 0 => Part.none
  | 1 => Part.some (g_val n)
  | c + 2 => Part.some c

def sepSmn (e x : ℕ) : ℕ :=
  match e with
  | 0 => 0
  | 1 => if x = 0 then 2 else if x = 1 then 1 else x + 2
  | c + 2 => c + 2

theorem sep_smn_spec (e x n : ℕ) :
    sepφ (sepSmn e x) n = sepφ e (Nat.pair x n) := by
  match e with
  | 0 => rfl
  | 1 =>
    simp only [sepSmn, sepφ]
    by_cases hx0 : x = 0
    · subst hx0; simp; exact (g_val_pair_zero n).symm
    · by_cases hx1 : x = 1
      · subst hx1; simp [hx0]; exact (g_val_pair_one n).symm
      · simp [hx0, hx1]
        match x, hx0, hx1 with
        | x + 2, _, _ => exact (g_val_pair_succ_succ x n).symm
  | c + 2 => rfl

noncomputable def sepAPS : IndexedAPS where
  φ := sepφ
  smn := sepSmn
  smn_spec := sep_smn_spec

/-! ## Diagonal is the identity -/

theorem sep_smn_diag (x : ℕ) : sepAPS.smn x x = x := by
  simp only [sepAPS, sepSmn]
  match x with
  | 0 => rfl
  | 1 => simp
  | _ + 2 => rfl

/-! ## Representability -/

theorem sep_rep_const (c : ℕ) :
    IndexedRepresentableUnary sepAPS (fun _ => c) :=
  ⟨c + 2, fun n => by simp [sepAPS, sepφ]⟩

theorem sep_rep_g :
    IndexedRepresentableUnary sepAPS g_val :=
  ⟨1, fun n => by simp [sepAPS, sepφ]⟩

theorem sep_representable_classification (h : ℕ → ℕ)
    (h_rep : IndexedRepresentableUnary sepAPS h) :
    (h = g_val) ∨ (∃ c, h = fun _ => c) := by
  obtain ⟨e, he⟩ := h_rep
  match e with
  | 0 =>
    exfalso; have := he 0; simp [sepAPS, sepφ] at this
  | 1 =>
    left; ext n; have := he n; simp [sepAPS, sepφ] at this; exact this.symm
  | c + 2 =>
    right; use c; ext n; have := he n; simp [sepAPS, sepφ] at this; exact this.symm

/-! ## I_rec -/

theorem sep_has_I_rec : IndexedHasRecursionTheorem sepAPS := by
  intro h h_smn_rep
  have h_diag : IndexedRepresentableUnary sepAPS h := by
    convert h_smn_rep using 1; ext x; rw [sep_smn_diag]
  rcases sep_representable_classification h h_diag with rfl | ⟨c, rfl⟩
  · -- h = g_val. Fixed point at e = 0: g_val(0) = 0, φ_0 = ⊥ = φ_{g_val(0)} = φ_0.
    exact ⟨0, fun n => by simp [sepAPS, sepφ, g_val_zero]⟩
  · -- h = const_c. Fixed point depends on c.
    match c with
    | 0 => exact ⟨0, fun n => by simp [sepAPS, sepφ]⟩
    | 1 => exact ⟨1, fun n => by simp [sepAPS, sepφ]⟩
    | c + 2 => exact ⟨c + 2, fun n => by simp [sepAPS, sepφ]⟩

/-! ## ¬I_comp -/

theorem sep_no_I_comp : ¬ Nonempty (IndexedHasRepresentableComp sepAPS) := by
  intro ⟨inst⟩
  obtain ⟨k, hk⟩ := inst.comp g_val sep_rep_g
  -- A tracker k must satisfy: φ_k(pair(0,0)) = φ_0(0) = ⊥ and φ_k(pair(pair(3,0),0)) = φ_3(0) = 1.
  -- Case analysis: k ∈ {0,1,c+2}. Each yields ⊥ = some or some = ⊥.
  have h0 := hk 0 0
  have h1 := hk (Nat.pair 3 0) 0
  rw [g_val_zero] at h0
  rw [show g_val (Nat.pair 3 0) = 3 from g_val_pair_succ_succ 1 0] at h1
  simp only [sepAPS, sepφ] at h0 h1
  match k with
  | 0 => exact absurd h1 (by simp)
  | 1 => exact absurd h0 (by simp)
  | k + 2 => exact absurd h0 (by simp)

/-! ## The separation theorem -/

/-- **I_rec does not imply I_comp in abstract IndexedAPS.** -/
theorem I_rec_not_implies_I_comp :
    ∃ aps : IndexedAPS,
      IndexedHasRecursionTheorem aps ∧
      ¬ Nonempty (IndexedHasRepresentableComp aps) :=
  ⟨sepAPS, sep_has_I_rec, sep_no_I_comp⟩

end APSUniformization
