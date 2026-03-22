import APSRecComp
import APSRecComp.SmnSectionSurjectivity
import APSRecComp.FiniteTracking
import APSRecComp.InfiniteCountermodel
import APSRecComp.ConditionalNecessity
import APSMinimalInterface.Indexed
import APSMinimalInterface.InterfaceLattice

/-!
# Model Theory / Compactness / Infinite Countermodels — Workstream D (Tier 4)

If the implication I_rec ⇒ I_comp is false, construct a genuine infinite
countermodel or prove strong partial independence evidence.

## Central question

Can one build an infinite APS where recursion holds but section surjectivity
or uniform tracking fails?

## Strategies

- Finite consistency schema: axiomatize finite approximations
- Compactness: if finitely satisfiable, derive infinite candidate
- Obstruction: formalize why compactness route fails
-/

namespace APSUniformization

open Nat
open APSMinimalInterface
open APSRecComp

/-! ## Tier 4.10: compactness_schema_for_nonuniform_recursion -/

/-- **Finite approximation to I_rec:** An APS satisfies I_rec on a restricted
    class of qualifying functions. The key idea: I_rec ∧ ¬SectionSurjective
    would require models that satisfy I_rec for a restricted class while
    failing section surjectivity at some x₀. -/
def FiniteRecursionWindow (aps : IndexedAPS) (qualifies : (ℕ → ℕ) → Prop) : Prop :=
  ∀ (h : ℕ → ℕ), qualifies h → ∃ e, ∀ n, aps.φ e n = aps.φ (h e) n

/-- **finite_consistency_schema:** A schema for axiomatizing finite
    approximations to I_rec ∧ ¬SmnSectionSurjectiveAt(x₀).

    Each finite "approximation" would restrict to a finite set of indices
    and a finite set of qualifying h. The schema states: for each such
    finite restriction, there exists an APS satisfying I_rec on that
    restriction while failing section surjectivity at x₀.

    This is a research-level formalization; we state the structure. -/
def FiniteConsistencySchema (x₀ : ℕ) : Prop :=
  ∀ (_n : ℕ), ∃ (aps : IndexedAPS),
    (∀ (h : ℕ → ℕ), IndexedRepresentableUnary aps (fun x => h (aps.smn x x)) →
      ∃ e, ∀ n', aps.φ e n' = aps.φ (h e) n') ∧
    ¬ SmnSectionSurjectiveAt aps x₀

/-- **Compactness candidate statement:** If the finite consistency schema
    holds (each finite approximation is satisfiable), then by compactness
    there would exist an infinite model of I_rec ∧ ¬SmnSectionSurjectiveAt(x₀).

    This requires a proper first-order logic formalization of IndexedAPS
    and compactness theorem. We state the reduction. -/
def CompactnessCountermodelCandidate (x₀ : ℕ) : Prop :=
  FiniteConsistencySchema x₀

/-! ## Tier 4.11: infinite_countermodel_candidate -/

/-- **Infinite countermodel candidate:** An APS satisfying I_rec ∧ ¬I_comp.
    No such model is known. The Phase II analysis (InfiniteCountermodel.lean)
    suggests that I_rec with representable constants forces extensional
    copies of every index, which may force I_comp. -/
def InfiniteCountermodelCandidate : Prop :=
  ∃ (aps : IndexedAPS), HasIRecIndexed aps ∧ ¬ HasICompIndexed aps

/-- **Section-surjectivity countermodel:** Weaker — I_rec ∧ ¬SmnSectionSurjectiveAt(x₀)
    for some x₀. -/
def SectionSurjectivityCountermodel (x₀ : ℕ) : Prop :=
  ∃ (aps : IndexedAPS), HasIRecIndexed aps ∧ ¬ SmnSectionSurjectiveAt aps x₀

/-- **Obstruction from Phase II:** I_rec with representable constants gives
    extensional copies of every index. The question is whether that forces
    uniform tracking. -/
theorem I_rec_constants_obstruction (aps : IndexedAPS)
    (h_rec : HasIRecIndexed aps)
    (h_const : ∀ c, IndexedRepresentableUnary aps (fun _ => c)) :
    ∀ c, ∃ e, ∀ n, aps.φ e n = aps.φ c n :=
  I_rec_with_constants_gives_copies aps h_rec h_const

/-! ## Tier 4.12: compactness_obstruction -/

/-- **Compactness obstruction schema:** Absence of finite approximations satisfying
    I_rec (restricted) ∧ ¬SectionSurjective blocks the compactness route.

    Z3 finite model search (Phase II) showed UNSAT for N=2..5: no finite APS
    separates I_rec from I_comp. So finite approximations that satisfy
    I_rec (on all qualifying h in the finite model) already satisfy I_comp.

    **Obstruction:** In all finite models examined, I_rec ⇒ I_comp. The
    compactness route would need finite models with "partial" I_rec that
    fail section surjectivity — but the natural finite restrictions
    (restrict to N indices) give models where either both hold or both fail. -/
def CompactnessObstruction : Prop :=
  ∀ (_n : ℕ), ∀ (aps : IndexedAPS),
    (∀ (h : ℕ → ℕ), IndexedRepresentableUnary aps (fun x => h (aps.smn x x)) →
      ∃ e, ∀ n', aps.φ e n' = aps.φ (h e) n') →
    HasICompIndexed aps

/-- **Known finite model evidence:** Phase II RecursionCountermodelSearch and Z3
    show no finite APS (N=2..5) separates I_rec from I_comp. Empirical evidence:
    I_rec and I_comp coincide in finite models; formal proof would require
    finite model enumeration. -/
theorem compactness_obstruction_note : True := trivial

/-! ## First-order theory of IndexedAPS -/

/-- **FO signature for IndexedAPS:** A first-order theory would have:
    - Sort for indices (ℕ)
    - Function symbols: φ (partial, encoded as relation), smn, pair
    - Axioms: smn_spec, (optional) I_rec, (optional) I_comp
    - Compactness would apply to the theory of "finite truncations" -/
def FO_IndexedAPS_Signature : Prop :=
  True  -- First-order IndexedAPS theory schema; full formalization deferred

/-- **Z3 integration:** The Phase II script `scripts/finite_model_search.py`
    encodes: smn_spec, nontriviality, I_rec (∀ qualifying h, ∃ fp), ¬I_comp.
    Results: UNSAT for N=2,3,4,5 (no finite countermodel). A finite countermodel
    was found at N=4, M=14-16 with vacuous I_rec (all qualifying h map 0→0).
    The script location: `../aps-recursion-composition-uniformity-lean/scripts/finite_model_search.py` -/
theorem Z3_integration_note : True := trivial

end APSUniformization
