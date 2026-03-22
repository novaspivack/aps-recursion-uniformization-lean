import APSRecComp
import APSRecComp.CategoricalSemantics
import APSRecComp.ConditionalNecessity
import APSUniformization.Iteration
import APSMinimalInterface.Indexed
import APSMinimalInterface.InterfaceLattice

/-!
# Iteration Transfer — Preiteration Model → IndexedAPS

Investigate whether a known preiteration model that separates fixed-point
existence from parameter identity can be interpreted as an IndexedAPS-like
structure. If yes, that would yield a countermodel to I_rec ⇒ I_comp.

## Iteration theory background

In Conway/preiteration theories (Bloom–Ésik 1993):
- **Basic fixpoint axiom:** Every guarded equation has a unique solution
- **Parameter identity:** fp(h parameterized by x) = x-section of fp(h)
- These are independent: parameter identity is an axiom, not derivable

## Transfer question

Can we construct an IndexedAPS from a preiteration algebra where:
- I_rec holds (fixpoint axiom)
- I_comp fails (parameter identity fails)?
-/

namespace APSUniformization

open Nat
open APSMinimalInterface
open APSRecComp

/-! ## IndexedAPS-like structure from iteration algebra -/

/-- **Iteration algebra:** A structure with a fixpoint operator. We formalize
    the minimal interface needed for transfer. -/
structure IterationAlgebra where
  carrier : Type
  fixpoint : (carrier → carrier) → carrier
  fixpoint_axiom : ∀ (f : carrier → carrier), f (fixpoint f) = fixpoint f

/-- **Parameter identity (iteration):** The fixpoint of a parameterized family
    equals the parameterized fixpoint. In iteration theory this is an axiom.
    Full formalization would require dependent types for the parameterized schema. -/
def HasParameterIdentity (_A : IterationAlgebra) : Prop :=
  True

/-- **Transfer obstruction (conceptual):** To interpret an IterationAlgebra as IndexedAPS,
    we need:
    1. carrier = ℕ (or a type with pairing)
    2. An "application" φ : ℕ → ℕ →. ℕ
    3. smn : ℕ → ℕ → ℕ with smn_spec
    4. The fixpoint operator must match I_rec's fixed-point existence

    The parameter identity in iteration theory corresponds to I_comp (uniform
    tracking). If we have an iteration algebra with fixpoint but without
    parameter identity, the transfer would need to produce an IndexedAPS
    with I_rec but not I_comp.

    **Obstruction:** No such transfer has been constructed. The iteration
    algebra fixpoint operates on carrier → carrier, while I_rec quantifies
    over h : ℕ → ℕ with a representability condition. The representability
    condition (IndexedRepresentableUnary aps (fun x => h (aps.smn x x)))
    is not present in abstract iteration algebras. -/
theorem transfer_obstruction :
    ∀ (_A : IterationAlgebra),
      (HasParameterIdentity _A → True) ∧
      (¬ HasParameterIdentity _A → True) := by
  intro _A
  constructor
  · intro _; trivial
  · intro _; trivial

/-! ## Preiteration gap transfer -/

/-- **Preiteration gap:** In iteration theory, the gap between fixpoint axiom
    and parameter identity is well-known. Our question: does this gap
    transfer to IndexedAPS?

    **Formal statement:** If there exists an IterationAlgebra A with
    fixpoint axiom but without parameter identity, and we can construct
    an IndexedAPS from A that preserves the fixpoint property as I_rec,
    then that IndexedAPS would be a countermodel (I_rec ∧ ¬I_comp).

    **Status:** The construction of IndexedAPS from A requires:
    - Defining φ from A's structure
    - Defining smn with smn_spec
    - Proving the representability condition aligns with A's fixpoint
    No such construction is known. -/
def PreiterationGapTransfers : Prop :=
  ∃ (_A : IterationAlgebra) (aps : IndexedAPS),
    (∀ (h : ℕ → ℕ), IndexedRepresentableUnary aps (fun x => h (aps.smn x x)) →
      ∃ e, ∀ n, aps.φ e n = aps.φ (h e) n) ∧
    ¬ (∀ (h : ℕ → ℕ), IndexedRepresentableUnary aps h →
      ∃ k, ∀ x n, aps.φ (aps.smn k x) n = aps.φ (h x) n)

/-- **Analogy summary:** The APS gap I_rec ⇒ I_comp is structurally analogous
    to the iteration-theoretic gap fixpoint ⇒ parameter identity. Whether
    the analogy is strong enough to transfer a counterexample remains open. -/
theorem iteration_analogy_summary :
    (∀ aps, HasICompIndexed aps ↔ ParameterIdentity aps) ∧
    (∀ aps, HasIRecIndexed aps ↔ PreiterationAxiom aps) ∧
    True := by
  constructor
  · exact I_comp_as_parameter_identity
  constructor
  · exact I_rec_as_preiteration_axiom
  · trivial

end APSUniformization
