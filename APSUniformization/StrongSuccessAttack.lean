import APSRecComp
import APSRecComp.SmnTracking
import APSRecComp.SmnSectionSurjectivity
import APSRecComp.FiniteTracking
import APSRecComp.ConditionalExactness
import APSRecComp.DensityAttack
import APSRecComp.InfiniteCountermodel
import APSRecComp.SmnReachability
import APSRecComp.ContrapositiveProof
import APSUniformization.CloneDictionary
import APSUniformization.Interpolation
import APSMinimalInterface.Indexed
import APSMinimalInterface.InterfaceLattice

/-!
# Strong Success Attack — Path to I_rec ⇒ I_comp

Consolidates the strongest conditional results and attacks the positive route.

## Strategy

1. **Conditional chain:** I_rec + I_diag + HasRepresentableConstants ⇒ pointwise reachability
2. **Gap:** Pointwise (∀ x, ∃ e_x) does not yield uniform (∃ k, ∀ x) without gluing
3. **Attack:** Find minimal X such that I_rec + X ⇒ I_comp
4. **Contrapositive:** Strengthen the conditional contrapositive
-/

namespace APSUniformization

open Nat
open APSMinimalInterface
open APSRecComp

/-! ## Strongest conditional theorem -/

/-- **I_rec + I_diag + constants ⇒ pointwise reachability:** For every h₀,
    each h₀(x) has an extensionally equal index. The uniformization to a single
    tracker k is the gap. -/
theorem I_rec_diag_constants_pointwise (aps : IndexedAPS)
    (h_rec : HasIRecIndexed aps) (_h_diag : HasIDiagIndexed aps)
    (h_const : ∀ c, IndexedRepresentableUnary aps (fun _ => c))
    (h₀ : ℕ → ℕ) :
    ∀ x, ∃ e, ∀ n, aps.φ e n = aps.φ (h₀ x) n :=
  family_of_fps aps h_rec _h_diag h₀ h_const

/-- **I_rec + constants ⇒ extensional copies:** Every index has an extensional
    copy. This is the "richness" that might force I_comp in infinite models. -/
theorem I_rec_constants_copies (aps : IndexedAPS)
    (h_rec : HasIRecIndexed aps)
    (h_const : ∀ c, IndexedRepresentableUnary aps (fun _ => c)) :
    ∀ c, ∃ e, ∀ n, aps.φ e n = aps.φ c n :=
  I_rec_with_constants_gives_copies aps h_rec h_const

/-! ## Minimal X for I_rec + X ⇒ I_comp -/

/-- **Outcome A minimal X:** The weakest natural X such that
    (I_rec + I_diag + constants + X) ⇒ I_comp is HasGluing.
    We already have: JointSmnSectionSurjective + HasGluing ⇒ I_comp.
    The open part: does I_rec + I_diag + constants ⇒ JointSmnSectionSurjective?
    Or does I_rec ⇒ HasGluing? -/
theorem minimal_X_characterization (aps : IndexedAPS) :
    (JointSmnSectionSurjective aps ∧ HasGluing aps → HasICompIndexed aps) ∧
    (HasFiniteTracking aps ∧ HasGluing aps → HasICompIndexed aps) := by
  constructor
  · intro ⟨h_joint, h_glue⟩
    exact joint_section_surj_plus_X_implies_comp aps h_joint h_glue
  · intro ⟨h_ft, h_glue⟩
    exact finite_tracking_plus_X_implies_global aps h_ft h_glue

/-! ## Section surjectivity from fixed-point density -/

/-- **Fixed-point density:** I_rec + constants gives fixed points for const_c
    for every c. So the set of fixed points (as extensional classes) includes
    every extensional class. The question: does the set of x₀-sections of fixed
    points cover all extensional classes? -/
theorem fp_density_from_constants (aps : IndexedAPS)
    (h_rec : HasIRecIndexed aps)
    (h_const : ∀ c, IndexedRepresentableUnary aps (fun _ => c)) :
    ∀ c, ∃ e, (∀ n, aps.φ e n = aps.φ c n) ∧
      (∀ x₀ n, aps.φ (aps.smn e x₀) n = aps.φ c (pair x₀ n)) := by
  intro c
  obtain ⟨e, he⟩ := I_rec_constants_copies aps h_rec h_const c
  exact ⟨e, he, fun x₀ n => by rw [aps.smn_spec]; exact he (pair x₀ n)⟩

/-- **Section surjectivity gap (restated):** The x₀-section of a fixed point
    e of const_c is n ↦ φ_c(pair(x₀, n)), not n ↦ φ_c(n). -/
theorem section_surj_gap_restated (aps : IndexedAPS) (c x₀ : ℕ)
    (e : ℕ) (h_fp : ∀ n, aps.φ e n = aps.φ c n) :
    ∀ n, aps.φ (aps.smn e x₀) n = aps.φ c (pair x₀ n) := by
  intro n
  rw [aps.smn_spec]
  exact h_fp (pair x₀ n)

/-! ## I_rec + I_diag ⇒ section match (strongest unconditional) -/

/-- **I_rec + I_diag ⇒ fixed-point section matching:** For every representable h,
    the fixed point e satisfies smn(e, x) ≃ smn(h(e), x) for all x. The obstruction:
    I_comp requires smn(k, x) ≃ h(x) for all x, not just matching at e. -/
theorem I_rec_diag_section_match (aps : IndexedAPS)
    (h_rec : HasIRecIndexed aps) (h_diag : HasIDiagIndexed aps)
    (h : ℕ → ℕ) (h_rep : IndexedRepresentableUnary aps h) :
    ∃ e, ∀ x n, aps.φ (aps.smn e x) n = aps.φ (aps.smn (h e) x) n := by
  have h_smn_rep := h_diag h h_rep
  obtain ⟨e, he⟩ := I_rec_gives_section_match aps h_rec h h_smn_rep
  exact ⟨e, he⟩

/-! ## Uniformization principle -/

/-- **Uniformization principle:** Pointwise trackers (∀ x, ∃ k_x) for representable h₀
    versus uniform tracker (∃ k, ∀ x). Equals HasGluing when the pointwise condition
    is finite tracking. -/
theorem uniformization_principle (aps : IndexedAPS) :
    HasGluing aps ↔
    ∀ (h₀ : ℕ → ℕ), IndexedRepresentableUnary aps h₀ →
      (∀ (F : Finset ℕ), ∃ k, ∀ x ∈ F, ∀ n, aps.φ (aps.smn k x) n = aps.φ (h₀ x) n) →
      ∃ k, ∀ x n, aps.φ (aps.smn k x) n = aps.φ (h₀ x) n :=
  gluing_iff_interpolation aps

/-! ## Strong success conditional -/

/-- **Strong success conditional:** I_rec + I_diag + constants + HasGluing ⇒ I_comp
    would hold IF pointwise reachability implied finite tracking. It does not:
    pointwise gives ∀ x, ∃ e_x, φ_{e_x} = φ_{h₀(x)}, but finite tracking needs
    ∃ k, ∀ x ∈ F, smn(k, x) ≃ h₀(x). The gap is uniformization: organizing
    {e_x} into an smn-family requires a universal evaluator. -/
theorem strong_success_requires_finite_tracking (aps : IndexedAPS) :
    HasFiniteTracking aps ∧ HasGluing aps → HasICompIndexed aps :=
  fun ⟨h_ft, h_glue⟩ => finite_tracking_plus_X_implies_global aps h_ft h_glue

/-! ## Obstruction: gluing cannot be derived from I_rec -/

/-- **Gluing is necessary:** I_comp implies gluing. Any proof of I_rec ⇒ I_comp
    must either establish I_rec ⇒ HasGluing or bypass gluing. -/
theorem gluing_necessary_for_strong_success (aps : IndexedAPS)
    (h_comp : HasICompIndexed aps) : HasGluing aps :=
  comp_implies_gluing aps h_comp

/-! ## Contrapositive: section failure ⇒ I_rec failure (under conditions) -/

/-- **Section failure obstructs fixed point's section:** If t is a witness
    (no k has smn(k, x₀) ≃ t), then any e with φ_e = φ_t satisfies
    smn(e, x₀) ≄ t. So fixed points of const_t don't achieve section surjectivity. -/
theorem section_failure_fp_obstruction (aps : IndexedAPS) (x₀ t e : ℕ)
    (h_fp : ∀ n, aps.φ e n = aps.φ t n)
    (h_fail_t : ∀ k, ∃ n, aps.φ (aps.smn k x₀) n ≠ aps.φ t n) :
    ∃ n, aps.φ (aps.smn e x₀) n ≠ aps.φ t n :=
  fp_of_const_not_section aps x₀ t e h_fp h_fail_t

/-- **Contrapositive reduction (sharp):** To prove I_rec ⇒ SmnSectionSurjectiveAt(x₀),
    assume ¬SmnSectionSurjectiveAt(x₀) and derive ¬I_rec. The obstruction:
    we need h with IndexedRepresentableUnary aps (fun x => h (aps.smn x x)) and
    no fixed point. The conditional_contrapositive identifies the exact
    representability/branching conditions needed. -/
theorem contrapositive_reduction_sharp (aps : IndexedAPS) (x₀ : ℕ) :
    (SmnSectionSurjectiveAt aps x₀ → True) ∧
    (¬ SmnSectionSurjectiveAt aps x₀ →
      ∃ t, ∀ k, ∃ n, aps.φ (aps.smn k x₀) n ≠ aps.φ t n) := by
  constructor
  · intro _; trivial
  · exact section_failure_witness aps x₀

/-! ## Infinite countermodel obstruction -/

/-- **I_rec + constants ⇒ extensional density:** In any APS with I_rec and
    representable constants, every extensional class has a representative.
    The infinite countermodel would need I_rec without constants, or a model
    where this density does not force I_comp. -/
theorem infinite_countermodel_obstruction (aps : IndexedAPS)
    (h_rec : HasIRecIndexed aps)
    (h_const : ∀ c, IndexedRepresentableUnary aps (fun _ => c)) :
    ∀ c, ∃ e, ∀ n, aps.φ e n = aps.φ c n :=
  I_rec_constants_copies aps h_rec h_const

end APSUniformization
