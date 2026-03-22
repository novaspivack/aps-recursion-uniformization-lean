import APSUniformization.TrackerFailureRel
import APSUniformization.FailureSetGeometry
import APSUniformization.GluingHierarchy
import APSUniformization.Interpolation
import APSRecComp
import APSMinimalInterface.Indexed

/-!
# Uniformization Principles — SPEC_V4 Taxonomy

Generalize existing candidates into a taxonomy:

- pointwise uniformization
- finite uniformization
- basin uniformization
- section amalgamation
- failure-set intersection

These are the missing algebraic/topological principles, no longer ad hoc lemmas.
-/

namespace APSUniformization

open Nat
open APSMinimalInterface
open APSRecComp

/-! ## Pointwise uniformization -/

/-- **Pointwise uniformization:** At each x, there exists k with smn(k,x) ≃ h₀(x).
    This is SmnSectionSurjectiveAt for each x. -/
def PointwiseUniformization (aps : IndexedAPS) : Prop :=
  ∀ (h₀ : ℕ → ℕ) (x : ℕ), ∃ k, ∀ n, aps.φ (aps.smn k x) n = aps.φ (h₀ x) n

/-- **Pointwise from section surjectivity:** If section surjective at every x,
    we have pointwise uniformization. -/
theorem section_surj_implies_pointwise (aps : IndexedAPS)
    (h : ∀ x₀, SmnSectionSurjectiveAt aps x₀) :
    PointwiseUniformization aps := by
  intro h₀ x
  exact h x (h₀ x)

/-! ## Finite uniformization -/

/-- **Finite uniformization:** For every finite F, there exists k tracking on F.
    This is HasFiniteTracking. -/
def FiniteUniformization (aps : IndexedAPS) : Prop :=
  HasFiniteTracking aps

theorem finite_uniformization_iff (aps : IndexedAPS) :
    FiniteUniformization aps ↔ HasFiniteTracking aps := Iff.rfl

/-! ## Basin uniformization -/

/-- **Basin uniformization:** A nonmeager fixed-point basin forces section
    surjectivity at that index. This is NonmeagerBasinImpliesSectionSurj. -/
def BasinUniformization (aps : IndexedAPS) (d : ℕ → ℕ) : Prop :=
  NonmeagerBasinImpliesSectionSurj aps d

/-- **Basin uniformization (all d):** For every diagonal d, basin uniformization. -/
def BasinUniformizationAll (aps : IndexedAPS) : Prop :=
  ∀ d, BasinUniformization aps d

/-! ## Section amalgamation -/

/-- **Section amalgamation:** When we have trackers k_F for each finite F,
    can we amalgamate them into a single global tracker? This is HasGluing. -/
def SectionAmalgamation (aps : IndexedAPS) : Prop :=
  HasGluing aps

theorem section_amalgamation_iff (aps : IndexedAPS) :
    SectionAmalgamation aps ↔ HasGluing aps := Iff.rfl

/-! ## Failure-set intersection -/

/-- **Failure-set intersection (pairwise):** When tracking fails, the failure
    sets F_k have pairwise nonempty intersection. -/
def FailureSetIntersectionPairwise (aps : IndexedAPS) : Prop :=
  ∀ (h₀ : ℕ → ℕ), ¬ SmnReachable aps h₀ →
    PairwiseFailureIntersection aps h₀

/-- **Failure-set intersection (finite):** When tracking fails, the failure
    sets have finite intersection property. -/
def FailureSetIntersectionFinite (aps : IndexedAPS) : Prop :=
  ∀ (h₀ : ℕ → ℕ), ¬ SmnReachable aps h₀ →
    FiniteFailureIntersection aps h₀

/-- **SectionFailureUniformizes as failure-set intersection:** The T7 quantifier
    swap says: when tracking fails, ∃ x₀, ∀ k, x₀ ∈ F_k. That is exactly
    ⋂_k F_k ≠ ∅. So SectionFailureUniformizes = global failure-set intersection. -/
theorem section_failure_uniformizes_iff_global_intersection (aps : IndexedAPS) :
    SectionFailureUniformizes aps ↔
    ∀ (h₀ : ℕ → ℕ), ¬ SmnReachable aps h₀ →
      ∃ x₀, ∀ k, TrackerFailureRel aps h₀ k x₀ := by
  constructor
  · intro h h₀ h_ntrack
    obtain ⟨x₀, hx₀⟩ := h h₀ h_ntrack
    exact ⟨x₀, fun k => hx₀ k⟩
  · intro h h₀ h_ntrack
    obtain ⟨x₀, hx₀⟩ := h h₀ h_ntrack
    exact ⟨x₀, fun k => hx₀ k⟩

/-! ## Taxonomy summary -/

/-- **Pointwise uniformization = section surjective everywhere.** -/
theorem pointwise_uniformization_iff (aps : IndexedAPS) :
    PointwiseUniformization aps ↔ ∀ x₀, SmnSectionSurjectiveAt aps x₀ := by
  constructor
  · intro h x₀ e
    obtain ⟨k, hk⟩ := h (fun _ => e) x₀
    exact ⟨k, hk⟩
  · intro h h₀ x
    exact h x (h₀ x)

/-- **Uniformization principle hierarchy:**
    - Pointwise: at each x, ∃ k matching
    - Finite: for each finite F, ∃ k matching on F
    - Section amalgamation: finite ⇒ global (HasGluing)
    - Failure-set intersection: when failure, F_k intersect
    - Basin: nonmeager basin ⇒ section surj -/
theorem uniformization_taxonomy (aps : IndexedAPS) :
    (PointwiseUniformization aps ↔ ∀ x₀, SmnSectionSurjectiveAt aps x₀) ∧
    (FiniteUniformization aps ↔ HasFiniteTracking aps) ∧
    (SectionAmalgamation aps ↔ HasGluing aps) := by
  exact ⟨pointwise_uniformization_iff aps, finite_uniformization_iff aps, section_amalgamation_iff aps⟩

end APSUniformization
