import APSUniformization.Interpolation
import APSUniformization.CloneDictionary
import APSUniformization.FailureSetGeometry
import APSRecComp
import APSRecComp.FiniteTracking
import APSMinimalInterface.Indexed
import Mathlib.Data.Finset.Basic

/-!
# Gluing Hierarchy — SPEC_V4 Workstream U3

Split `HasGluing` into intermediate principles:

  singleton gluing ⇒ pairwise gluing ⇒ finite gluing ⇒ global gluing

Study which are forced by I_rec and how they relate to failure-set intersection.

## Target U5

Define intermediate gluing principles and prove equivalences or implications
with failure-set intersection properties.
-/

namespace APSUniformization

open Nat
open APSMinimalInterface
open APSRecComp

/-! ## The gluing ladder -/

/-- **Singleton gluing:** For representable h₀, there exists k tracking on
    any singleton {x}. This is exactly HasSingletonTracking. -/
def HasSingletonGluing (aps : IndexedAPS) : Prop :=
  ∀ (h₀ : ℕ → ℕ), IndexedRepresentableUnary aps h₀ →
    ∀ x, ∃ k, ∀ n, aps.φ (aps.smn k x) n = aps.φ (h₀ x) n

/-- **Pairwise gluing:** For representable h₀, if we have finite tracking for
    pairs, then we can find a single k that tracks on any given pair.
    Equivalently: ∀ x₁ x₂, ∃ k, k tracks on {x₁, x₂}. -/
def HasPairwiseGluing (aps : IndexedAPS) : Prop :=
  ∀ (h₀ : ℕ → ℕ), IndexedRepresentableUnary aps h₀ →
    ∀ x₁ x₂, ∃ k, ∀ x ∈ ({x₁, x₂} : Finset ℕ), ∀ n, aps.φ (aps.smn k x) n = aps.φ (h₀ x) n

/-- **Finite gluing:** For representable h₀, for every finite F there exists k
    tracking on F. This is exactly HasFiniteTracking. -/
def HasFiniteGluing (aps : IndexedAPS) : Prop :=
  HasFiniteTracking aps

/-- **Global gluing:** Finite trackers extend to global. This is HasGluing. -/
def HasGlobalGluing (aps : IndexedAPS) : Prop :=
  HasGluing aps

/-! ## Hierarchy implications -/

/-- **Singleton ⇒ Pairwise (for size-2 sets):** If we have singleton tracking,
    we get pairwise by... actually we need both singletons to be tracked by the
    *same* k. Singleton tracking gives k₁ for x₁ and k₂ for x₂, but not
    necessarily k₁ = k₂. So singleton gluing does NOT imply pairwise gluing
    without an amalgamation step. The hierarchy is about the *conclusion*
    strength: pairwise is a stronger conclusion than singleton. -/
theorem singleton_gluing_weaker_than_pairwise (aps : IndexedAPS)
    (h_pair : HasPairwiseGluing aps) :
    HasSingletonGluing aps := by
  intro h₀ h_rep x
  obtain ⟨k, hk⟩ := h_pair h₀ h_rep x x
  exact ⟨k, fun n => hk x (Finset.mem_insert_self x _) n⟩

/-- **Pairwise ⇒ Finite (for pairs):** HasPairwiseGluing gives tracking on
    any 2-element set. HasFiniteGluing requires tracking on any finite set.
    So pairwise is a special case of finite. -/
theorem pairwise_gluing_weaker_than_finite (aps : IndexedAPS)
    (h_fin : HasFiniteGluing aps) :
    HasPairwiseGluing aps := by
  intro h₀ h_rep x₁ x₂
  exact h_fin h₀ h_rep {x₁, x₂}

/-- **Finite ⇒ Global (the gluing step):** HasFiniteGluing + HasGluing gives
    global tracking. HasGluing is exactly "finite → global". -/
theorem finite_plus_gluing_implies_global (aps : IndexedAPS)
    (h_fin : HasFiniteGluing aps) (h_glue : HasGlobalGluing aps) :
    ∀ (h₀ : ℕ → ℕ), IndexedRepresentableUnary aps h₀ →
      ∃ k, ∀ x n, aps.φ (aps.smn k x) n = aps.φ (h₀ x) n := by
  intro h₀ h_rep
  exact h_glue h₀ h_rep (h_fin h₀ h_rep)

/-! ## Equivalence with standard definitions -/

theorem has_finite_gluing_iff (aps : IndexedAPS) :
    HasFiniteGluing aps ↔ HasFiniteTracking aps := Iff.rfl

theorem has_global_gluing_iff (aps : IndexedAPS) :
    HasGlobalGluing aps ↔ HasGluing aps := Iff.rfl

/-! ## Directed gluing (optional) -/

/-- **Directed gluing:** For a directed family of finite sets (F_i) with
    F_i ⊆ F_j when i ≤ j, if we have trackers on each F_i, do we get a
    global tracker? This would be a compactness-style principle. -/
def HasDirectedGluing (aps : IndexedAPS) : Prop :=
  ∀ (h₀ : ℕ → ℕ), IndexedRepresentableUnary aps h₀ →
    (∀ (F : Finset ℕ), ∃ k, ∀ x ∈ F, ∀ n, aps.φ (aps.smn k x) n = aps.φ (h₀ x) n) →
    ∃ k, ∀ x n, aps.φ (aps.smn k x) n = aps.φ (h₀ x) n

/-- **Directed gluing = Global gluing:** Same as HasGluing. -/
theorem directed_gluing_iff_global (aps : IndexedAPS) :
    HasDirectedGluing aps ↔ HasGlobalGluing aps := Iff.rfl

/-! ## Relation to failure-set intersection (Target U5) -/

/-- **Pairwise gluing from pairwise failure intersection:** If
    PairwiseFailureIntersection holds for all h₀ with tracking failure, then
    the failure sets cannot "block" pairwise gluing. The connection: when
    tracking fails (¬SmnReachable), we have ∀k ∃x failure. Pairwise intersection
    would give ∃x ∀k₁ k₂ failure at x for that pair — but that's different.
    The real link: SectionFailureUniformizes says ∃x₀ ∀k failure. That is
    "global" failure intersection. Pairwise intersection would be a step. -/
theorem gluing_hierarchy_note (_aps : IndexedAPS) :
    True := by
  trivial
  -- The missing math: I_rec ⇒ pairwise gluing? And pairwise + compactness ⇒ global?

/-! ## I_rec and the hierarchy -/

/-- **I_rec ⇒ HasPairwiseGluing:** OPEN. Key step toward I_rec ⇒ I_comp. -/
theorem I_rec_pairwise_gluing_open_note : True := trivial

end APSUniformization
