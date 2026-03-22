import APSRecComp
import APSRecComp.SmnTracking
import APSRecComp.ConditionalNecessity
import APSRecComp.CategoricalSemantics
import APSRecComp.ParameterizedRecursion
import APSRecComp.RecursionTaxonomy
import APSMinimalInterface.Indexed
import APSMinimalInterface.InterfaceLattice

/-!
# Iteration / Conway / Parameter Identity Translation — Workstream C (Tier 3)

Make the iteration-theory analogy precise. The APS gap may be an instance of
the gap between fixed-point existence and the parameter identity.

## Central question

Is the APS gap exactly an instance of the gap between fixed-point existence
and the parameter identity / functoriality / Bekič-like laws?
-/

namespace APSUniformization

open Nat
open APSMinimalInterface
open APSRecComp

/-! ## Iteration-theoretic analogues -/

/-- **Preiteration axiom (fixed-point existence):** Every qualifying endomorphism
    has a fixed point. This is I_rec. -/
def PreiterationAxiom (aps : IndexedAPS) : Prop :=
  HasIRecIndexed aps

/-- **Parameter identity (uniform parameterization):** For every representable h,
    there exists k whose smn-family tracks h. This is I_comp / SmnTrackingForRep. -/
def ParameterIdentity (aps : IndexedAPS) : Prop :=
  SmnTrackingForRep aps

/-- **smn_spec as parameterization schema:** The specialization law that
    generates the parameterized families. -/
def ParameterizationSchema (_aps : IndexedAPS) : Prop :=
  True  -- smn_spec is built into IndexedAPS; schema for parameterization

/-! ## Tier 3.7: I_rec_parameter_identity_bridge -/

/-- **I_rec_as_preiteration_axiom:** I_rec is exactly the preiteration fixed-point
    axiom for the smn-generated structure. -/
theorem I_rec_as_preiteration_axiom (aps : IndexedAPS) :
    HasIRecIndexed aps ↔ PreiterationAxiom aps :=
  Iff.rfl

/-- **I_comp_as_parameter_identity:** I_comp is exactly the parameter identity
    (uniform tracking for representable functions). -/
theorem I_comp_as_parameter_identity (aps : IndexedAPS) :
    HasICompIndexed aps ↔ ParameterIdentity aps :=
  corrected_exactness_iff aps

/-- **smn_spec_as_parameterization_schema:** smn_spec provides the coherence
    for parameterization: φ(smn e x)(n) = φ e (pair x n). -/
theorem smn_spec_as_parameterization_schema (aps : IndexedAPS) (e x n : ℕ) :
    aps.φ (aps.smn e x) n = aps.φ e (pair x n) :=
  aps.smn_spec e x n

/-- **aps_parameter_identity_bridge:** The open question I_rec ⇒ I_comp is
    equivalent to: does the preiteration axiom force the parameter identity?
    In iteration theory, fixed-point existence does NOT imply parameter identity
    in general. The APS question is whether smn_spec adds enough structure. -/
theorem aps_parameter_identity_bridge (aps : IndexedAPS) :
    (PreiterationAxiom aps → ParameterIdentity aps) ↔
    (HasIRecIndexed aps → HasICompIndexed aps) := by
  rw [I_comp_as_parameter_identity]
  rfl

/-! ## Tier 3.8: I_comp_parameter_identity_equiv -/

/-- **I_comp_parameter_identity_equiv:** I_comp and ParameterIdentity are
    equivalent (corrected exactness). -/
theorem I_comp_parameter_identity_equiv (aps : IndexedAPS) :
    HasICompIndexed aps ↔ ParameterIdentity aps :=
  corrected_exactness_iff aps

/-! ## Tier 3.9: preiteration_gap_model_or_obstruction -/

/-- **Preiteration gap:** In general preiteration theories, fixed-point
    existence (PreiterationAxiom) does not imply parameter identity.
    The gap is: one fixed point per h vs uniform family per h.

    **Obstruction:** minimalIndexedAPS has WeakIndexedRecursion (one h has fp)
    but not FullIndexedRecursion. So even "one fp" vs "all fps" can separate.
    The full gap (FullIndexedRecursion vs ParameterIdentity) remains open.

    **Model transfer:** If a preiteration model separates fixed-point from
    parameter identity, it could potentially be interpreted as an IndexedAPS.
    No such transfer has been constructed. -/
theorem preiteration_gap_structure (aps : IndexedAPS) :
    -- Parameter identity ⇒ preiteration (I_comp + I_diag ⇒ I_rec)
    (ParameterIdentity aps → HasIDiagIndexed aps → PreiterationAxiom aps) ∧
    -- The converse is the open question
    True := by
  constructor
  · intro h_param h_diag
    rw [← I_comp_as_parameter_identity] at h_param
    exact I_comp_and_diag_implies_rec aps h_param h_diag
  · trivial

/-- **Full parameterized recursion as parameter identity:** HasFullParameterizedRecursion
    gives uniform fixed points; it implies I_rec but is distinct from SmnTracking.
    SmnTracking says smn(k,x) ≃ h(x); FullParamRec says smn(k,x) is a fixed point of h. -/
theorem full_param_rec_implies_preiteration (aps : IndexedAPS) :
    HasFullParameterizedRecursion aps → PreiterationAxiom aps :=
  full_parameterized_rec_implies_rec aps

end APSUniformization
