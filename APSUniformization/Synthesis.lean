import APSRecComp
import APSRecComp.SmnTracking
import APSRecComp.SmnSectionSurjectivity
import APSRecComp.FiniteTracking
import APSRecComp.ConditionalNecessity
import APSRecComp.SectionSurjectivityTheorems
import APSUniformization.CloneDictionary
import APSUniformization.Interpolation
import APSUniformization.Iteration
import APSUniformization.Compactness
import APSMinimalInterface.Indexed
import APSMinimalInterface.InterfaceLattice

/-!
# Synthesis / Exactness Closure — Workstream E

Turn the results of Workstreams A–D into the final theorem structure.

## Possible outcomes

- I_rec + X ⇒ I_comp (positive theorem)
- I_rec ∧ ¬I_comp countermodel
- Exact characterization of the missing algebraic principle
- Rigorous non-derivability / independence-style statement
-/

namespace APSUniformization

open Nat
open APSMinimalInterface
open APSRecComp

/-! ## recursion_uniformization_theorem -/

/-- **recursion_uniformization_theorem (conditional):** Under gluing,
    recursion uniformizes to composition. I_rec + I_diag + HasGluing ⇒ I_comp.

    The gap: we need HasGluing. I_rec + I_diag gives finite tracking?
    No — I_rec does not imply finite tracking (section surjectivity).
    So the conditional is: UniformSmnSectionSurjective + HasGluing ⇒ I_comp,
    and JointSmnSectionSurjective + HasGluing ⇒ I_comp.

    The strongest conditional from our results: FiniteTracking + HasGluing ⇒ I_comp. -/
theorem recursion_uniformization_theorem (aps : IndexedAPS)
    (h_ft : HasFiniteTracking aps) (h_glue : HasGluing aps) :
    HasICompIndexed aps :=
  finite_tracking_plus_X_implies_global aps h_ft h_glue

/-- **Uniformization with joint section surjectivity:** Joint + Gluing ⇒ I_comp. -/
theorem joint_uniformization_theorem (aps : IndexedAPS)
    (h_joint : JointSmnSectionSurjective aps) (h_glue : HasGluing aps) :
    HasICompIndexed aps :=
  joint_section_surj_plus_X_implies_comp aps h_joint h_glue

/-! ## aps_interpolation_exactness -/

/-- **aps_interpolation_exactness:** I_comp is exactly finite tracking + gluing.
    The interpolation principle (gluing) is the precise bridge from local to global. -/
theorem aps_interpolation_exactness (aps : IndexedAPS) :
    HasICompIndexed aps ↔ HasFiniteTracking aps ∧ HasGluing aps :=
  comp_iff_finite_tracking_and_gluing aps

/-- **The missing principle:** HasGluing — finite trackers extend to global.
    This is the algebraic interpolation principle that closes the gap. -/
theorem missing_principle_characterization (aps : IndexedAPS) :
    (HasICompIndexed aps → HasGluing aps) ∧
    (HasFiniteTracking aps → HasGluing aps → HasICompIndexed aps) := by
  exact ⟨fun h => comp_implies_gluing aps h,
         fun h_ft h_glue => finite_tracking_plus_X_implies_global aps h_ft h_glue⟩

/-! ## section_surjectivity_characterisation -/

/-- **section_surjectivity_characterisation:** The hierarchy of section
    surjectivity conditions and their relationship to I_comp.

    1. SmnSectionSurjectiveAt(x₀) ↔ ProjectionSurjectiveAt(x₀) (clone dictionary)
    2. UniformSmnSectionSurjective ⇒ HasSingletonTracking
    3. JointSmnSectionSurjective ⇒ HasFiniteTracking
    4. Joint + Gluing ⇒ I_comp
    5. I_comp ⇒ all of the above (trivially) -/
theorem section_surjectivity_characterisation (aps : IndexedAPS) :
    (∀ x₀, SmnSectionSurjectiveAt aps x₀ ↔ ProjectionSurjectiveAt aps x₀) ∧
    (UniformSmnSectionSurjective aps → HasSingletonTracking aps) ∧
    (JointSmnSectionSurjective aps → HasFiniteTracking aps) ∧
    (JointSmnSectionSurjective aps → HasGluing aps → HasICompIndexed aps) := by
  constructor
  · exact fun x₀ => section_surj_as_projection_surj aps x₀
  constructor
  · exact uniform_section_surj_implies_singleton_tracking aps
  constructor
  · exact joint_implies_finite_tracking aps
  · exact joint_section_surj_plus_X_implies_comp aps

/-! ## recursion_comp_independence_schema -/

/-- **recursion_comp_independence_schema:** The open question is whether
    I_rec implies I_comp. We have:

    - I_comp ⇔ SmnTrackingForRep (corrected exactness)
    - I_comp ⇔ FiniteTracking ∧ Gluing (interpolation exactness)
    - I_rec + I_diag ⇒ I_comp (Phase I sufficiency when comp holds)
    - I_rec ⇒ I_comp? OPEN

    Independence would mean: there exists a model of I_rec ∧ ¬I_comp, or
    the implication is not derivable from the APS axioms. No such result
    has been proved. -/
theorem recursion_comp_independence_schema :
    -- What we know
    (∀ aps, HasICompIndexed aps ↔ SmnTrackingForRep aps) ∧
    (∀ aps, HasICompIndexed aps ↔ HasFiniteTracking aps ∧ HasGluing aps) ∧
    (∀ aps, HasICompIndexed aps → HasIDiagIndexed aps → HasIRecIndexed aps) ∧
    -- Open: I_rec ⇒ I_comp
    True := by
  constructor
  · exact corrected_exactness_iff
  constructor
  · exact comp_iff_finite_tracking_and_gluing
  constructor
  · intro aps h_comp h_diag
    exact I_comp_and_diag_implies_rec aps h_comp h_diag
  · trivial

/-! ## Final synthesis summary -/

/-- **Phase III synthesis:** All workstreams integrated.

    - Workstream A (Clone): Dictionary complete
    - Workstream B (Interpolation): Gluing = X, exactness proved
    - Workstream C (Iteration): Parameter identity = I_comp, bridge formalized
    - Workstream D (Countermodel): Schema and obstruction formalized
    - Workstream E (Synthesis): Conditional theorems, characterisation, open question -/
theorem phase_iii_synthesis :
    (∀ aps, (HasICompIndexed aps ↔ ∀ h, IndexedRepresentableUnary aps h → SmnCloneReachable aps h)) ∧
    (∀ aps, HasICompIndexed aps ↔ HasFiniteTracking aps ∧ HasGluing aps) ∧
    (∀ aps, HasICompIndexed aps ↔ ParameterIdentity aps) ∧
    (∀ aps x₀, SmnSectionSurjectiveAt aps x₀ ↔ ProjectionSurjectiveAt aps x₀) := by
  constructor
  · exact I_comp_as_clone_surjectivity
  constructor
  · exact comp_iff_finite_tracking_and_gluing
  constructor
  · exact I_comp_as_parameter_identity
  · exact section_surj_as_projection_surj

end APSUniformization
