import APSRecComp
import APSRecComp.SmnTracking
import APSRecComp.SmnSectionSurjectivity
import APSRecComp.FiniteTracking
import APSRecComp.SectionSurjectivityTheorems
import APSRecComp.ConditionalNecessity
import APSUniformization.CloneDictionary
import APSMinimalInterface.Indexed
import APSMinimalInterface.InterfaceLattice

/-!
# Interpolation / Baker–Pixley Route — Workstream B (Tier 2)

Determine whether some local-to-global interpolation theorem can force global
tracking from finite tracking.

## Central question

Is there an analogue of Baker–Pixley (local agreement on finite sets implies
global term representability) for the smn-generated operation system?

## Candidate hypotheses for X

- Gluing: finite trackers extend to global
- Joint section surjectivity: one k matches targets on finite F
- Representable witnesses / near-unanimity-like structure
-/

namespace APSUniformization

open Nat
open APSMinimalInterface
open APSRecComp

/-! ## Tier 2.4: finite_tracking_plus_X_implies_global -/

/-- **Gluing condition X:** Finite trackers for representable h₀ extend to a
    global tracker. This is the minimal X that bridges finite → global. -/
def HasGluing (aps : IndexedAPS) : Prop :=
  ∀ (h₀ : ℕ → ℕ), IndexedRepresentableUnary aps h₀ →
    (∀ (F : Finset ℕ), ∃ k, ∀ x ∈ F, ∀ n, aps.φ (aps.smn k x) n = aps.φ (h₀ x) n) →
    ∃ k, ∀ x n, aps.φ (aps.smn k x) n = aps.φ (h₀ x) n

/-- **finite_tracking_plus_X_implies_global:** Finite tracking + gluing ⇒ I_comp.
    X = HasGluing. The gluing step is exactly the local-to-global interpolation. -/
theorem finite_tracking_plus_X_implies_global (aps : IndexedAPS)
    (h_ft : HasFiniteTracking aps) (h_glue : HasGluing aps) :
    HasICompIndexed aps :=
  finite_tracking_and_gluing_implies_comp aps h_ft h_glue

/-- **Gluing is necessary:** I_comp implies gluing (trivially: take F = univ).
    So gluing is the exact interpolation principle for finite → global. -/
theorem comp_implies_gluing (aps : IndexedAPS) (h_comp : HasICompIndexed aps) :
    HasGluing aps := by
  intro h₀ h₀_rep _
  obtain ⟨k, hk⟩ := (corrected_exactness_iff aps).mp h_comp h₀ h₀_rep
  exact ⟨k, fun x n => hk x n⟩

/-- **Gluing ⇔ the interpolation principle:** HasGluing is equivalent to
    "finite tracking extends to global" for representable h₀. -/
theorem gluing_iff_interpolation (aps : IndexedAPS) :
    HasGluing aps ↔
    ∀ (h₀ : ℕ → ℕ), IndexedRepresentableUnary aps h₀ →
      (∀ (F : Finset ℕ), ∃ k, LocalInterpolatesAt aps h₀ k F) →
      SmnCloneInterpolates aps h₀ := by
  constructor
  · intro h_glue h₀ h₀_rep h_ft
    exact h_glue h₀ h₀_rep (fun F => h_ft F)
  · intro h_int h₀ h₀_rep h_ft
    exact h_int h₀ h₀_rep (fun F => h_ft F)

/-! ## Tier 2.5: joint_section_surj_plus_X_implies_comp -/

/-- **joint_section_surj_plus_X_implies_comp:** Joint section surjectivity +
    gluing ⇒ I_comp. X = HasGluing. -/
theorem joint_section_surj_plus_X_implies_comp (aps : IndexedAPS)
    (h_joint : JointSmnSectionSurjective aps) (h_glue : HasGluing aps) :
    HasICompIndexed aps :=
  joint_section_surj_and_gluing_implies_comp aps h_joint h_glue

/-- **Joint ⇒ finite tracking:** Joint section surjectivity alone gives
    finite tracking (one k per finite F). Gluing upgrades to global. -/
theorem joint_implies_finite_tracking (aps : IndexedAPS)
    (h_joint : JointSmnSectionSurjective aps) : HasFiniteTracking aps :=
  joint_section_surj_implies_finite_tracking aps h_joint

/-! ## Tier 2.6: baker_pixley_candidate_X -/

/-- **Baker–Pixley candidate X:** The condition that local agreement on finite
    sets implies global term realizability. For the smn-clone, the candidate
    is HasGluing: finite trackers (local agreement) extend to global tracker
    (global term). -/
def BakerPixleyCandidate (aps : IndexedAPS) : Prop :=
  HasGluing aps

/-- **no_baker_pixley_without_X:** Without gluing, finite tracking does NOT
    imply global. The minimalIndexedAPS has UniformSmnSectionSurjective false,
    so it fails finite tracking. For APS that have finite tracking but not
    I_comp, gluing would be the missing ingredient.

    Formal statement: If an APS has finite tracking but not I_comp, then it
    fails gluing. So gluing is necessary for finite → global. -/
theorem no_baker_pixley_without_X (aps : IndexedAPS)
    (h_ft : HasFiniteTracking aps) (h_ncomp : ¬ HasICompIndexed aps) :
    ¬ HasGluing aps := by
  intro h_glue
  exact h_ncomp (finite_tracking_plus_X_implies_global aps h_ft h_glue)

/-- **Gluing is the exact interpolation principle:** I_comp ↔ (FiniteTracking ∧ Gluing).
    The forward direction: I_comp gives finite tracking (trivial) and gluing (comp_implies_gluing).
    The backward: finite_tracking_plus_X_implies_global. -/
theorem comp_iff_finite_tracking_and_gluing (aps : IndexedAPS) :
    HasICompIndexed aps ↔ HasFiniteTracking aps ∧ HasGluing aps := by
  constructor
  · intro h_comp
    constructor
    · intro h₀ h₀_rep F
      obtain ⟨k, hk⟩ := (corrected_exactness_iff aps).mp h_comp h₀ h₀_rep
      exact ⟨k, fun x _ n => hk x n⟩
    · exact comp_implies_gluing aps h_comp
  · intro ⟨h_ft, h_glue⟩
    exact finite_tracking_plus_X_implies_global aps h_ft h_glue

end APSUniformization
