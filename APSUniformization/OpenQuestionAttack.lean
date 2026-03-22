import APSRecComp
import APSRecComp.SmnTracking
import APSRecComp.SmnSectionSurjectivity
import APSRecComp.ContrapositiveProof
import APSRecComp.ConditionalNecessity
import APSRecComp.CardinalityArgument
import APSRecComp.CardinalityProof
import APSRecComp.SmnReachability
import APSUniformization.CloneDictionary
import APSUniformization.Interpolation
import APSUniformization.Iteration
import APSMinimalInterface.Indexed
import APSMinimalInterface.InterfaceLattice

/-!
# Open Question Attack — I_rec ⇒ I_comp

New attack attempts on the recursion–composition frontier.

## Attack 1: On-diagonal unification

The collapse theorem (off_diagonal_fp_obstruction) shows: off-diagonal universal
fixed points force APS collapse. So in nontrivial APS, fixed points are either
distributed or on-diagonal. The standard proof (with I_comp) produces on-diagonal
fixed points e = smn(k, k). Can we show I_rec forces on-diagonal fixed points?

## Attack 2: Parameter identity as X

I_rec + ParameterIdentity ⇒ I_comp (trivial: ParameterIdentity = I_comp).
The question: does I_rec + some WEAKER parameter-identity-like condition ⇒ I_comp?

## Attack 3: Section surjectivity from fixed-point density

If fixed points are "dense" in the sense that for every extensional class,
some fixed point of some h has that class as its x₀-section, then section
surjectivity holds. The cardinality argument suggests continuum-many h
share countably many fixed points — could this density force section surjectivity?
-/

namespace APSUniformization

open Nat
open APSMinimalInterface
open APSRecComp

/-! ## Attack 1: On-diagonal structure -/

/-- **On-diagonal fixed point gives family match:** If e = smn(x₀, x₀) is a
    fixed point of h, then smn(e, x) ≃ smn(h(e), x) for all x. The fixed point's
    smn-family equals h(e)'s smn-family. -/
theorem on_diagonal_fp_gives_family_match (aps : IndexedAPS) (h : ℕ → ℕ) (x₀ : ℕ)
    (h_fp : ∀ n, aps.φ (aps.smn x₀ x₀) n = aps.φ (h (aps.smn x₀ x₀)) n) :
    ∀ x n, aps.φ (aps.smn (aps.smn x₀ x₀) x) n = aps.φ (aps.smn (h (aps.smn x₀ x₀)) x) n := by
  intro x n
  rw [aps.smn_spec (aps.smn x₀ x₀) x n, aps.smn_spec (h (aps.smn x₀ x₀)) x n]
  exact h_fp (pair x n)

/-- **Unification gap:** Per-x₀ trackers (one k_x per x) yield finite tracking
    on singletons, but gluing (finite → global) is a separate step. HasGluing
    is the exact condition that bridges this gap. -/
theorem per_point_implies_singleton_tracking (aps : IndexedAPS) (h : ℕ → ℕ)
    (h_per_point : ∀ x₀, ∃ k, ∀ n, aps.φ (aps.smn k x₀) n = aps.φ (h (aps.smn x₀ x₀)) n) :
    ∀ x₀, ∃ k, SingletonTracks aps (fun x => h (aps.smn x x)) k x₀ :=
  fun x₀ => by
    obtain ⟨k, hk⟩ := h_per_point x₀
    exact ⟨k, hk⟩

/-! ## Attack 2: Natural X candidates -/

/-- **RepresentableGluing:** The gluing function (finite → global) is representable.
    Too strong — essentially I_comp. Placeholder for structural analysis. -/
def RepresentableGluing (aps : IndexedAPS) : Prop :=
  HasGluing aps ∧ ∃ (e : ℕ), ∀ n, aps.φ e n = aps.φ e n  -- structural schema; second conjunct trivial

/-- **JointSectionSurjective as X:** I_rec + JointSmnSectionSurjective + Gluing ⇒ I_comp.
    Proved in Interpolation. The open part: does I_rec ⇒ JointSmnSectionSurjective? -/
theorem joint_plus_gluing_implies_comp (aps : IndexedAPS)
    (h_joint : JointSmnSectionSurjective aps) (h_glue : HasGluing aps) :
    HasICompIndexed aps :=
  joint_section_surj_plus_X_implies_comp aps h_joint h_glue

/-! ## Attack 3: Contrapositive structure -/

/-- **Section failure ⇒ fixed-point obstruction:** If section surjectivity fails
    at x₀ for target t, then any fixed point e of const_t has smn(e, x₀) ≄ t.
    So the fixed point's x₀-section is wrong. -/
theorem section_failure_obstructs_fp (aps : IndexedAPS) (x₀ t e : ℕ)
    (_h_fp : ∀ n, aps.φ e n = aps.φ t n)
    (h_fail : ∀ k, ∃ n, aps.φ (aps.smn k x₀) n ≠ aps.φ t n) :
    ∃ n, aps.φ (aps.smn e x₀) n ≠ aps.φ t n :=
  h_fail e

/-- **The contrapositive reduction:** To prove I_rec ⇒ SmnSectionSurjectiveAt(x₀),
    it suffices to show: ¬SmnSectionSurjectiveAt(x₀) ⇒ ¬I_rec. The obstruction:
    we need to construct an h with representable diagonal but no fixed point,
    using the section failure. The conditional_contrapositive in Phase II
    identifies the branching condition needed. -/
theorem contrapositive_reduction (aps : IndexedAPS) (x₀ : ℕ) :
    (SmnSectionSurjectiveAt aps x₀ → True) ∧
    (¬ SmnSectionSurjectiveAt aps x₀ →
      ∃ t, ∀ k, ∃ n, aps.φ (aps.smn k x₀) n ≠ aps.φ t n) := by
  constructor
  · intro _; trivial
  · intro h_fail
    exact section_failure_witness aps x₀ h_fail

/-! ## Summary: structural picture -/

/-- **Open question decomposition:**
    1. I_rec ⇒ SmnSectionSurjectiveAt(x₀)? (OPEN — section_surj_gap)
    2. Uniform section surj ⇒ singleton tracking (PROVED)
    3. Finite tracking + Gluing ⇒ I_comp (PROVED)
    4. I_rec ⇒ on-diagonal fixed points? (PARTIAL — collapse theorem constrains)
    5. On-diagonal + unification ⇒ I_comp? (OPEN — pairing shift) -/
theorem open_question_decomposition :
    (∀ aps, UniformSmnSectionSurjective aps → HasSingletonTracking aps) ∧
    (∀ aps, HasFiniteTracking aps → HasGluing aps → HasICompIndexed aps) ∧
    True := by
  constructor
  · exact uniform_section_surj_implies_singleton_tracking
  constructor
  · exact finite_tracking_plus_X_implies_global
  · trivial

end APSUniformization
