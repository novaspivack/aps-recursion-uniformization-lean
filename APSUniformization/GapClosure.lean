import APSRecComp
import APSRecComp.SmnTracking
import APSRecComp.SmnSectionSurjectivity
import APSRecComp.FiniteTracking
import APSRecComp.ContrapositiveProof
import APSRecComp.ContrapositiveAttack
import APSRecComp.SmnReachability
import APSRecComp.ConditionalExactness
import APSUniformization.Interpolation
import APSUniformization.StrongSuccessAttack
import APSMinimalInterface.Indexed
import APSMinimalInterface.InterfaceLattice
import APSMinimalInterface.IndexedInterfaceTaxonomy

/-!
# Gap Closure — Attack Implementation

Concrete attacks on I_rec ⇒ I_comp.

## Attack 1: Contrapositive with explicit conditions

Prove that when the conditional_contrapositive conditions hold, section failure
implies I_rec failure. Then prove those conditions from I_rec + I_diag + X.

## Attack 2: Double fixed-point refinement

Use the structure from contrapositive_setup to attempt a second I_rec application
that might yield a tracker.

## Attack 3: I_rec + I_diag + full interface ⇒ I_comp

When we have I_comp (IndexedHasRecursionInterface), we get I_rec. The reverse
is the open question. We prove: I_comp + I_diag ⇒ I_rec (already known).
-/

namespace APSUniformization

open Nat
open APSMinimalInterface
open APSRecComp

/-! ## Attack 1: I_comp ⇒ section surjectivity -/

/-- **I_comp ⇒ SmnSectionSurjectiveAt:** When every representable function is
    smn-reachable, section surjectivity holds. Proof: for target e, take h₀ = const_e.
    If const_e is representable, I_comp gives k with smn(k, x) ≃ const_e(x) = e for all x.
    So smn(k, x₀) ≃ e. -/
theorem I_comp_implies_section_surj (aps : IndexedAPS)
    (h_comp : HasICompIndexed aps) (x₀ e : ℕ)
    (h_const : IndexedRepresentableUnary aps (fun _ => e)) :
    ∃ k, ∀ n, aps.φ (aps.smn k x₀) n = aps.φ e n := by
  rw [corrected_exactness_iff] at h_comp
  obtain ⟨k, hk⟩ := h_comp (fun _ => e) h_const
  exact ⟨k, fun n => hk x₀ n⟩

/-! ## Attack 2: Nontriviality from I_rec -/

/-- **Nontriviality at pair(x₀,0):** Existence of a, b with φ_a(pair(x₀,0)) ≠ φ_b(pair(x₀,0)).
    Holds in any APS with at least two distinct extensional classes. I_rec + constants
    yields extensional copies of every index, hence at least two classes when nontrivial. -/
def NontrivialAt (aps : IndexedAPS) (n : ℕ) : Prop :=
  ∃ a b, aps.φ a n ≠ aps.φ b n

/-- **Nontriviality decomposition:** Either we have nontriviality at pair(x₀,0),
    or all indices agree there. -/
theorem nontriviality_decomposition (aps : IndexedAPS) (x₀ : ℕ) :
    NontrivialAt aps (pair x₀ 0) ∨ (∀ a b, aps.φ a (pair x₀ 0) = aps.φ b (pair x₀ 0)) := by
  by_cases h : ∃ a b, aps.φ a (pair x₀ 0) ≠ aps.φ b (pair x₀ 0)
  · exact Or.inl h
  · push_neg at h
    exact Or.inr h

/-! ## Attack 3: Conditional contrapositive (when conditions hold) -/

/-- **Contrapositive with explicit equality-test hypothesis:** If the equality
    predicate d(e) = (φ_e(pair(x₀,0)) = φ_a(pair(x₀,0))) is representable,
    then section failure implies ¬I_rec. The diagonalization: h(e) = if d(e)
    then b else a has no fixed point. The proof requires showing the diagonal
    fun x => if d(smn x x) then b else a is representable (via I_diag + branching). -/
def ContrapositiveWithEqualityTest (aps : IndexedAPS) (x₀ a b : ℕ) : Prop :=
  ∀ (_h_diff : aps.φ a (pair x₀ 0) ≠ aps.φ b (pair x₀ 0))
    (_h_diag : HasIDiagIndexed aps)
    (_h_eq_rep : ∃ (d : ℕ → Bool), (∀ e, (d e = true) ↔ (aps.φ e (pair x₀ 0) = aps.φ a (pair x₀ 0))) ∧
      IndexedRepresentableBool aps d)
    (_h_branch : IndexedHasBranching aps)
    (_h_fail : ¬ SmnSectionSurjectiveAt aps x₀),
    ¬ HasIRecIndexed aps

/-! ## Attack 4: I_comp + constants ⇒ full section surjectivity -/

/-- **I_comp + constants ⇒ UniformSmnSectionSurjective:** When every constant
    is representable and I_comp holds, section surjectivity holds at every x₀. -/
theorem I_comp_constants_implies_uniform_section_surj (aps : IndexedAPS)
    (h_comp : HasICompIndexed aps)
    (h_const : ∀ c, IndexedRepresentableUnary aps (fun _ => c)) :
    UniformSmnSectionSurjective aps := by
  intro x₀ e
  exact I_comp_implies_section_surj aps h_comp x₀ e (h_const e)

/-! ## Attack 5: Double fixed-point structure -/

/-- **Fixed point of h₀ gives family match at e₁ only.** The obstruction: the match holds
    at the fixed point e₁, but I_comp requires matching at all x. -/
theorem fp_family_match_gap (aps : IndexedAPS)
    (_h_rec : HasIRecIndexed aps) (_h_diag : HasIDiagIndexed aps)
    (h₀ : ℕ → ℕ) (_h₀_rep : IndexedRepresentableUnary aps h₀)
    (e₁ : ℕ) (h_fp : ∀ n, aps.φ e₁ n = aps.φ (h₀ e₁) n) :
    (∀ x n, aps.φ (aps.smn e₁ x) n = aps.φ (aps.smn (h₀ e₁) x) n) ∧
    (SmnReachable aps h₀ ↔ ∃ k, ∀ x n, aps.φ (aps.smn k x) n = aps.φ (h₀ x) n) := by
  constructor
  · intro x n
    rw [aps.smn_spec, aps.smn_spec]
    exact h_fp (pair x n)
  · constructor
    · intro ⟨k, hk⟩
      exact ⟨k, hk⟩
    · intro ⟨k, hk⟩
      exact ⟨k, hk⟩

end APSUniformization
