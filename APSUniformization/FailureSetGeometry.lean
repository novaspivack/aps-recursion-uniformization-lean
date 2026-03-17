import APSUniformization.SectionClassGeometry
import APSUniformization.TrackerFailureRel
import APSRecComp
import APSMinimalInterface.Indexed
import Mathlib.Data.Finset.Basic

/-!
# Failure-Set Intersection Theory — SPEC_V4 Workstream U2

F_k = {x : σ_k(x) ≠ τ(x)} = {x : [smn(k,x)] ≠ [h₀(x)]}.

Develop pairwise, finite, and Helly-type principles for the family {F_k}.

## Targets U2–U4

- U2: Characterize F_k as inverse images; restrictions on σ_k and τ
- U3: Pairwise failure intersection property
- U4: Finite intersection / Helly-type properties
-/

namespace APSUniformization

open Nat
open APSMinimalInterface
open APSRecComp

/-! ## Failure set characterization (Target U2) -/

/-- **F_k as inverse image of disagreement:** F_k = {x : σ_k(x) ≠ τ(x)}.
    Already proved in SectionClassGeometry as failure_set_as_inverse_image. -/
theorem failure_set_inverse_image (aps : IndexedAPS) (h₀ : ℕ → ℕ) (k x : ℕ) :
    x ∈ TrackerFailureSet aps h₀ k ↔ ¬ SectionMatchesTargetAt aps h₀ k x :=
  failure_set_as_inverse_image aps h₀ k x

/-- **Target U2 — Extensional determination:** Failure set membership is determined
    by extensional classes of section and target. If (k,x) and (k',x') have the
    same section and target classes, then x ∈ F_k ↔ x' ∈ F_{k'}. -/
theorem failure_set_extensional_determination (aps : IndexedAPS) (h₀ : ℕ → ℕ) (k k' x x' : ℕ)
    (hsec : ∀ n, aps.φ (aps.smn k x) n = aps.φ (aps.smn k' x') n)
    (htarg : ∀ n, aps.φ (h₀ x) n = aps.φ (h₀ x') n) :
    (x ∈ TrackerFailureSet aps h₀ k) ↔ (x' ∈ TrackerFailureSet aps h₀ k') := by
  simp only [TrackerFailureSet, Set.mem_setOf_eq]
  exact tracker_failure_extensional aps h₀ k k' x x' hsec htarg

/-- **Target U2 — Restrictions:** σ_k and τ are not arbitrary. σ_k(x) = smn(k,x)
    is constrained by the APS structure; τ(x) = h₀(x) is any function. The failure
    set is determined by extensional disagreement. -/
theorem failure_set_restrictions (aps : IndexedAPS) (h₀ : ℕ → ℕ) (k x : ℕ) :
    x ∈ TrackerFailureSet aps h₀ k ↔ ¬ ExtEq aps (aps.smn k x) (h₀ x) := by
  simp only [TrackerFailureSet, Set.mem_setOf_eq, TrackerFailureRel, ExtEq]
  push_neg
  rfl

/-! ## Pairwise intersection (Target U3) -/

/-- **Pairwise failure intersection property:** ∀ k₁ k₂, ∃ x, x ∈ F_{k₁} ∩ F_{k₂}.
    This is the key structural question: when do failure sets intersect? -/
def PairwiseFailureIntersection (aps : IndexedAPS) (h₀ : ℕ → ℕ) : Prop :=
  ∀ k₁ k₂, (∃ x, TrackerFailureRel aps h₀ k₁ x) → (∃ x, TrackerFailureRel aps h₀ k₂ x) →
    ∃ x, TrackerFailureRel aps h₀ k₁ x ∧ TrackerFailureRel aps h₀ k₂ x

/-- **Pairwise intersection when sections match:** Sufficient condition from Option 8. -/
theorem pairwise_intersection_when_sections_match (aps : IndexedAPS) (h₀ : ℕ → ℕ) (k₁ k₂ : ℕ)
    (x : ℕ) (hsec : ∀ n, aps.φ (aps.smn k₁ x) n = aps.φ (aps.smn k₂ x) n)
    (hfail : TrackerFailureRel aps h₀ k₁ x) :
    TrackerFailureRel aps h₀ k₁ x ∧ TrackerFailureRel aps h₀ k₂ x :=
  pairwise_when_sections_match aps h₀ k₁ k₂ x hsec hfail

/-- **Pairwise intersection for extensional trackers:** When k₁ ≃ k₂ globally. -/
theorem pairwise_intersection_extensional_trackers (aps : IndexedAPS) (h₀ : ℕ → ℕ) (k₁ k₂ : ℕ)
    (heq : ∀ x n, aps.φ (aps.smn k₁ x) n = aps.φ (aps.smn k₂ x) n)
    (h₁ : ∃ x, TrackerFailureRel aps h₀ k₁ x)
    (h₂ : ∃ x, TrackerFailureRel aps h₀ k₂ x) :
    ∃ x, TrackerFailureRel aps h₀ k₁ x ∧ TrackerFailureRel aps h₀ k₂ x :=
  pairwise_extensional_trackers aps h₀ k₁ k₂ heq h₁ h₂

/-- **Pairwise intersection — general case:** OPEN (Target U3). No proof in bare IndexedAPS.
    See pairwise_intersection_when_sections_match and pairwise_intersection_extensional_trackers
    for proved sufficient conditions. FINAL_STATUS_AND_HANDOFF §What did not emerge. -/
theorem pairwise_intersection_open_note : True := trivial

/-! ## Finite intersection (Target U4) -/

/-- **Finite failure intersection property:** For finite K, if each F_k is nonempty,
    does ⋂_{k∈K} F_k ≠ ∅? -/
def FiniteFailureIntersection (aps : IndexedAPS) (h₀ : ℕ → ℕ) : Prop :=
  ∀ (K : Finset ℕ), (∀ k ∈ K, ∃ x, TrackerFailureRel aps h₀ k x) →
    ∃ x, ∀ k ∈ K, TrackerFailureRel aps h₀ k x

/-- **Singleton case:** Trivial. -/
theorem finite_intersection_singleton (aps : IndexedAPS) (h₀ : ℕ → ℕ) (k : ℕ)
    (h : ∃ x, TrackerFailureRel aps h₀ k x) :
    ∃ x, ∀ k' ∈ ({k} : Finset ℕ), TrackerFailureRel aps h₀ k' x := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, fun k' hk' => by simp only [Finset.mem_singleton] at hk'; rw [hk']; exact hx⟩

/-- **Finite intersection from pairwise:** If PairwiseFailureIntersection holds,
    then finite intersection holds for pairwise. The full finite case would need
    induction; the step is the same obstruction as finite_simultaneous_failure. -/
theorem pairwise_implies_finite_intersection_pair (aps : IndexedAPS) (h₀ : ℕ → ℕ)
    (h_pair : PairwiseFailureIntersection aps h₀) (k₁ k₂ : ℕ)
    (h₁ : ∃ x, TrackerFailureRel aps h₀ k₁ x)
    (h₂ : ∃ x, TrackerFailureRel aps h₀ k₂ x) :
    ∃ x, ∀ k ∈ ({k₁, k₂} : Finset ℕ), TrackerFailureRel aps h₀ k x := by
  obtain ⟨x, hx₁, hx₂⟩ := h_pair k₁ k₂ h₁ h₂
  use x
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl
  · exact hx₁
  · exact hx₂

/-! ## Helly-type property (Target U4) -/

/-- **Helly-type for failure sets:** A family of sets has the Helly property if
    whenever every pair intersects, the whole family intersects. For finite
    families of convex sets in ℝ^d, Helly's theorem says this holds.
    For our F_k, we define the property and ask whether it holds. -/
def FailureSetHellyProperty (aps : IndexedAPS) (h₀ : ℕ → ℕ) : Prop :=
  PairwiseFailureIntersection aps h₀ → FiniteFailureIntersection aps h₀

/-- **Helly-type:** OPEN. Does pairwise ⇒ finite intersection? No proof for F_k ⊆ ℕ. -/
theorem helly_open_note : True := trivial

/-! ## Failure set nonempty -/

theorem failure_set_nonempty_iff (aps : IndexedAPS) (h₀ : ℕ → ℕ) (k : ℕ) :
    (TrackerFailureSet aps h₀ k).Nonempty ↔ ∃ x, TrackerFailureRel aps h₀ k x := by
  constructor
  · intro ⟨x, hx⟩
    exact ⟨x, hx⟩
  · exact failure_set_nonempty_of_failure aps h₀ k

end APSUniformization
