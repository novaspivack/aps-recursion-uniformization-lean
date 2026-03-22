import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic.Linarith

/-!
# GVal Realization — Concrete definition discharging the 5 axioms

g_val strips leading 1s from the pair tree:
  g_val(pair(0,n)) = 0
  g_val(pair(1,n)) = g_val(n)
  g_val(pair(c+2,n)) = c+2
  g_val(0) = 0
-/

namespace APSUniformization

open Nat

/-! ## Well-foundedness -/

private theorem unpair_snd_lt {n : ℕ} (hn : n ≠ 0) (ha : (Nat.unpair n).1 = 1) :
    (Nat.unpair n).2 < n := by
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  have h_pair_eq := Nat.pair_unpair n
  have h_lt_pair : Nat.pair 0 (Nat.unpair n).2 < Nat.pair 1 (Nat.unpair n).2 :=
    Nat.pair_lt_pair_left _ (by omega)
  have h_eq : Nat.pair (Nat.unpair n).1 (Nat.unpair n).2 = n := h_pair_eq
  rw [ha] at h_eq
  have h_snd_le_pair0 : (Nat.unpair n).2 ≤ Nat.pair 0 (Nat.unpair n).2 :=
    Nat.right_le_pair 0 (Nat.unpair n).2
  linarith

/-! ## Concrete definition -/

/-- g_val_def: strips leading 1s from the pair tree. -/
def g_val_def : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    if h : (Nat.unpair (n + 1)).1 = 1 then
      have : (Nat.unpair (n + 1)).2 < n + 1 := unpair_snd_lt (by omega) h
      g_val_def (Nat.unpair (n + 1)).2
    else
      (Nat.unpair (n + 1)).1

private theorem g_val_def_unfold (n : ℕ) (hn : n ≠ 0) :
    g_val_def n = if (Nat.unpair n).1 = 1 then g_val_def (Nat.unpair n).2
                  else (Nat.unpair n).1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [g_val_def]

/-! ## The 5 properties -/

theorem g_val_def_zero : g_val_def 0 = 0 := by simp [g_val_def]

theorem g_val_def_pair_zero (n : ℕ) : g_val_def (Nat.pair 0 n) = 0 := by
  by_cases h : Nat.pair 0 n = 0
  · rw [h]; simp [g_val_def]
  · rw [g_val_def_unfold _ h, Nat.unpair_pair]; simp

theorem g_val_def_pair_one (n : ℕ) : g_val_def (Nat.pair 1 n) = g_val_def n := by
  have hne : Nat.pair 1 n ≠ 0 := by
    have := Nat.left_le_pair 1 n; omega
  rw [g_val_def_unfold _ hne, Nat.unpair_pair]; simp

theorem g_val_def_pair_succ_succ (c n : ℕ) : g_val_def (Nat.pair (c + 2) n) = c + 2 := by
  have hne : Nat.pair (c + 2) n ≠ 0 := by
    have := Nat.left_le_pair (c + 2) n; omega
  rw [g_val_def_unfold _ hne, Nat.unpair_pair]
  have : ¬(c + 2 = 1) := by omega
  rw [if_neg this]

end APSUniformization
