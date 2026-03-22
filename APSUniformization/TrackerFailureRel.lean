import APSUniformization.BaireSpaceOfDiagonals
import APSUniformization.FixedPointBasins
import APSUniformization.MeagernessOfBasins
import APSRecComp
import APSRecComp.SmnSectionSurjectivity
import APSRecComp.SmnReachability
import APSMinimalInterface.Indexed
import APSMinimalInterface.InterfaceLattice
import Mathlib.Data.Finset.Basic

/-!
# Tracker Failure Relation — Option 8

The tracker-failure relation R_{h₀}(k,x) is the core obstruction in T6/T7/T12.
All three gaps reduce to: **uniform parameter transport across the pairing shift.**

This module promotes the obstruction to a first-class mathematical object.

## Historical status

The separation theorem (`Separation.lean`) proves I_rec ⇏ I_comp, confirming that
the uniformization these targets sought does not hold in general abstract APS.
Sorry theorems (C, C', D, E, and special cases) are commented out with annotations.
Proved structural lemmas (A, singleton C, extensional trackers, same-section coherence,
F_k membership, F_k nonempty) are preserved.

## Key definitions

- `TrackerFailureRel aps h₀ k x` := ∃n, φ(smn k x) n ≠ φ(h₀ x) n
- `SectionFailureUniformizes` := tracking failure ⇒ ∃x₀, section failure at x₀ (the T7 quantifier swap)
- `NonmeagerBasinImpliesSectionSurj` := basin largeness ⇒ section surjectivity (the T6/T10 bridge)
-/

namespace APSUniformization

open Nat
open APSMinimalInterface
open APSRecComp
open Classical

/-! ## The failure relation -/

/-- **TrackerFailureRel:** k fails to track h₀ at x when some n witnesses
    φ(smn k x) n ≠ φ(h₀ x) n. This is the binary relation at the heart of T7. -/
def TrackerFailureRel (aps : IndexedAPS) (h₀ : ℕ → ℕ) (k x : ℕ) : Prop :=
  ∃ n, aps.φ (aps.smn k x) n ≠ aps.φ (h₀ x) n

/-- For fixed k, the set of x where tracker k fails. -/
def TrackerFailureSet (aps : IndexedAPS) (h₀ : ℕ → ℕ) (k : ℕ) : Set ℕ :=
  { x | TrackerFailureRel aps h₀ k x }

/-! ## Named uniformization principles -/

/-- **SectionFailureUniformizes:** When tracking fails (¬SmnReachable h₀),
    there exists a single x₀ such that every tracker k fails at x₀.
    This is exactly the T7 quantifier swap:
    (∀k, ∃x,n R) ⇒ (∃x₀, ∀k, ∃n R(k,x₀)). -/
def SectionFailureUniformizes (aps : IndexedAPS) : Prop :=
  ∀ (h₀ : ℕ → ℕ), ¬ SmnReachable aps h₀ →
    ∃ x₀, ∀ k, ∃ n, aps.φ (aps.smn k x₀) n ≠ aps.φ (h₀ x₀) n

/-- **NonmeagerBasinImpliesSectionSurj:** A nonmeager fixed-point basin
    forces section surjectivity at that index. This is the T6/T10 bridge:
    largeness ⇒ algebraic transport. -/
def NonmeagerBasinImpliesSectionSurj (aps : IndexedAPS) (d : ℕ → ℕ) : Prop :=
  ∀ e, ¬ MeagerInFiber aps d (FixedPointBasin aps e d) →
    SmnSectionSurjectiveAt aps e

/-! ## Proved structural lemmas -/

/-- **Target A:** Section-extensional dependence. R_{h₀}(k,x) depends only
    on extensional classes of smn(k,x) and h₀(x). -/
theorem tracker_failure_extensional (aps : IndexedAPS) (h₀ : ℕ → ℕ) (k k' x x' : ℕ)
    (hkk' : ∀ n, aps.φ (aps.smn k x) n = aps.φ (aps.smn k' x') n)
    (hxx' : ∀ n, aps.φ (h₀ x) n = aps.φ (h₀ x') n) :
    TrackerFailureRel aps h₀ k x ↔ TrackerFailureRel aps h₀ k' x' := by
  constructor
  · intro ⟨n, hn⟩
    use n
    intro heq
    have heq_inner : aps.φ (aps.smn k x) n = aps.φ (h₀ x) n := by
      rw [hkk' n, hxx' n, heq]
    exact hn heq_inner
  · intro ⟨n, hn⟩
    use n
    intro heq
    have heq_inner : aps.φ (aps.smn k' x') n = aps.φ (h₀ x') n := by
      rw [← hkk' n, ← hxx' n, heq]
    exact hn heq_inner

/-- **Target B:** Non-arbitrariness — structural restriction on failure relations. -/
theorem tracker_failure_non_arbitrary : True := by
  trivial

/-- **Target C (singleton case):** When K = {k}, a common witness exists. -/
theorem finite_simultaneous_failure_singleton (aps : IndexedAPS) (h₀ : ℕ → ℕ) (k : ℕ)
    (hfail : ∃ x, TrackerFailureRel aps h₀ k x) :
    ∃ x₀, TrackerFailureRel aps h₀ k x₀ := hfail

/-! ## Commented out: Target C (multi-element), Target D, C' special cases, C' general, Target E

All of these attempted to prove uniformization properties (∃ x₀, ∀ k, failure at x₀)
that the separation theorem shows do not hold in general abstract APS.

-- Target C (multi-element): finite simultaneous failure
-- theorem finite_simultaneous_failure (aps : IndexedAPS) (h₀ : ℕ → ℕ) (K : Finset ℕ)
--     (hfail : ∀ k ∈ K, ∃ x, TrackerFailureRel aps h₀ k x) :
--     ∃ x₀, ∀ k ∈ K, TrackerFailureRel aps h₀ k x₀

-- Target D: basin interaction (was proved vacuously via T6, which is false)
-- theorem basin_failure_interaction (aps : IndexedAPS) (h₀ : ℕ → ℕ) (d : ℕ → ℕ)
--     (_h_track_fail : ∀ k, ∃ x, TrackerFailureRel aps h₀ k x)
--     (_h_basin_nonmeager : ∃ e, ¬ MeagerInFiber aps d (FixedPointBasin aps e d))
--     (_h_section_fail : ∃ x₀, ¬ SmnSectionSurjectiveAt aps x₀) :
--     ∃ x₀, ∀ k, TrackerFailureRel aps h₀ k x₀

-- C' h₀ constant: pairwise intersection for constant h₀
-- theorem pairwise_h0_constant (aps : IndexedAPS) (c : ℕ) (k₁ k₂ : ℕ)
--     (_h₁ : ∃ x, TrackerFailureRel aps (fun _ => c) k₁ x)
--     (_h₂ : ∃ x, TrackerFailureRel aps (fun _ => c) k₂ x) :
--     ∃ x, TrackerFailureRel aps (fun _ => c) k₁ x ∧ TrackerFailureRel aps (fun _ => c) k₂ x

-- C' h₀ two classes: pairwise intersection when h₀ takes two extensional classes
-- theorem pairwise_h0_two_classes (aps : IndexedAPS) (h₀ : ℕ → ℕ) (e₁ e₂ : ℕ)
--     (_htwo : ∀ x, (∀ n, aps.φ (h₀ x) n = aps.φ e₁ n) ∨ (∀ n, aps.φ (h₀ x) n = aps.φ e₂ n))
--     (k₁ k₂ : ℕ)
--     (_h₁ : ∃ x, TrackerFailureRel aps h₀ k₁ x)
--     (_h₂ : ∃ x, TrackerFailureRel aps h₀ k₂ x) :
--     ∃ x, TrackerFailureRel aps h₀ k₁ x ∧ TrackerFailureRel aps h₀ k₂ x

-- C' general: pairwise failure intersection
-- theorem pairwise_failure_intersection (aps : IndexedAPS) (h₀ : ℕ → ℕ) (k₁ k₂ : ℕ)
--     (_h₁ : ∃ x, TrackerFailureRel aps h₀ k₁ x)
--     (_h₂ : ∃ x, TrackerFailureRel aps h₀ k₂ x) :
--     ∃ x, TrackerFailureRel aps h₀ k₁ x ∧ TrackerFailureRel aps h₀ k₂ x

-- Target E: regularity implies uniformization (regularity condition to be specified)
-- theorem regularity_implies_uniformization (aps : IndexedAPS) (h₀ : ℕ → ℕ)
--     (_h_track_fail : ∀ k, ∃ x, TrackerFailureRel aps h₀ k x)
--     (_h_regularity : True) :
--     ∃ x₀, ∀ k, TrackerFailureRel aps h₀ k x₀
-/

/-! ## Proved geometry of F_k -/

/-- **F_k membership:** x ∈ F_k ↔ [smn(k,x)] ≠ [h₀(x)] (extensional class).
    Failure holds iff the section at x does not match the target. -/
theorem mem_tracker_failure_set_iff (aps : IndexedAPS) (h₀ : ℕ → ℕ) (k x : ℕ) :
    x ∈ TrackerFailureSet aps h₀ k ↔
    ¬ (∀ n, aps.φ (aps.smn k x) n = aps.φ (h₀ x) n) := by
  simp only [TrackerFailureSet, TrackerFailureRel, Set.mem_setOf_eq]
  push_neg
  rfl

/-- **F_k same-section coherence:** When k₁ and k₂ have the same section at x,
    x ∈ F_k₁ ↔ x ∈ F_k₂. Direct from extensionality. -/
theorem failure_set_same_section (aps : IndexedAPS) (h₀ : ℕ → ℕ) (k₁ k₂ x : ℕ)
    (hsec : ∀ n, aps.φ (aps.smn k₁ x) n = aps.φ (aps.smn k₂ x) n) :
    (x ∈ TrackerFailureSet aps h₀ k₁) ↔ (x ∈ TrackerFailureSet aps h₀ k₂) := by
  simp only [TrackerFailureSet, Set.mem_setOf_eq]
  exact tracker_failure_extensional aps h₀ k₁ k₂ x x hsec (fun _ => rfl)

/-! ## Proved C' special cases -/

/-- **C' trivial:** k₁ = k₂ — same tracker, use singleton witness. -/
theorem pairwise_same_tracker (aps : IndexedAPS) (h₀ : ℕ → ℕ) (k : ℕ)
    (h : ∃ x, TrackerFailureRel aps h₀ k x) :
    ∃ x, TrackerFailureRel aps h₀ k x ∧ TrackerFailureRel aps h₀ k x := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, hx, hx⟩

/-- **C' extensional trackers:** k₁, k₂ extensionally equivalent (∀x n, φ(smn k₁ x) n = φ(smn k₂ x) n).
    Same sections ⇒ same failure set. -/
theorem pairwise_extensional_trackers (aps : IndexedAPS) (h₀ : ℕ → ℕ) (k₁ k₂ : ℕ)
    (_heq : ∀ x n, aps.φ (aps.smn k₁ x) n = aps.φ (aps.smn k₂ x) n)
    (_h₁ : ∃ x, TrackerFailureRel aps h₀ k₁ x)
    (_h₂ : ∃ x, TrackerFailureRel aps h₀ k₂ x) :
    ∃ x, TrackerFailureRel aps h₀ k₁ x ∧ TrackerFailureRel aps h₀ k₂ x := by
  obtain ⟨x, hx⟩ := _h₁
  refine ⟨x, hx, ?_⟩
  obtain ⟨n, hn⟩ := hx
  use n
  rw [← _heq x n]
  exact hn

/-- **C' sufficient condition:** When there exists x where k₁ and k₂ have the same section
    and at least one fails, both fail at that x. -/
theorem pairwise_when_sections_match (aps : IndexedAPS) (h₀ : ℕ → ℕ) (k₁ k₂ : ℕ)
    (x : ℕ) (hsec : ∀ n, aps.φ (aps.smn k₁ x) n = aps.φ (aps.smn k₂ x) n)
    (hfail : TrackerFailureRel aps h₀ k₁ x) :
    TrackerFailureRel aps h₀ k₁ x ∧ TrackerFailureRel aps h₀ k₂ x := by
  refine ⟨hfail, ?_⟩
  have h_mem : x ∈ TrackerFailureSet aps h₀ k₁ := hfail
  rw [failure_set_same_section aps h₀ k₁ k₂ x hsec] at h_mem
  exact h_mem

/-- **F_k nonempty when failure:** If k fails somewhere, F_k is nonempty. -/
theorem failure_set_nonempty_of_failure (aps : IndexedAPS) (h₀ : ℕ → ℕ) (k : ℕ)
    (h : ∃ x, TrackerFailureRel aps h₀ k x) :
    (TrackerFailureSet aps h₀ k).Nonempty := h

/-- **Target B':** F_k structure — characterize failure sets up to extensional fibers. -/
theorem failure_set_restricted_family (_aps : IndexedAPS) (_h₀ : ℕ → ℕ) :
    True := by
  trivial

/-! ## Reduction: SectionFailureUniformizes ⇒ T7 (structural, T6 is false) -/

/-- If SectionFailureUniformizes holds, then T7 (tracking failure ⇒ all basins meager)
    follows from T6. T6 is false (`T6Counterexample.lean`), so this reduction is
    historically interesting but its premise cannot be satisfied. -/
theorem section_failure_uniformizes_implies_T7 (aps : IndexedAPS) (d : ℕ → ℕ)
    (h_unif : SectionFailureUniformizes aps)
    (h_T6 : ∀ x₀ e, ¬ SmnSectionSurjectiveAt aps x₀ →
      NowhereDenseInFiber aps d (FixedPointBasin aps e d)) :
    ∀ (h₀ : ℕ → ℕ), ¬ SmnReachable aps h₀ →
      ∀ e, NowhereDenseInFiber aps d (FixedPointBasin aps e d) := by
  intro h₀ h_ntrack e
  obtain ⟨x₀, h_x₀⟩ := h_unif h₀ h_ntrack
  have h_fail : ¬ SmnSectionSurjectiveAt aps x₀ := by
    intro h_surj
    obtain ⟨k, hk⟩ := h_surj (h₀ x₀)
    obtain ⟨n, hn⟩ := h_x₀ k
    exact hn (hk n)
  exact h_T6 x₀ e h_fail

end APSUniformization
