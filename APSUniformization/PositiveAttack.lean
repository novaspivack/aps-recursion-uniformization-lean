import APSRecComp
import APSRecComp.SmnSectionSurjectivity
import APSRecComp.SmnReachability
import APSUniformization.Interpolation
import APSUniformization.GapClosure
import APSMinimalInterface.Indexed
import APSMinimalInterface.InterfaceLattice

/-!
# Option A: Positive Route Attacks

1. Representable second projection: if (unpair n).2 is representable, can we unshift?
2. Fixed-point encoding: design h whose fixed point gives the section
3. I_rec ⇒ HasGluing: direct derivation
-/

namespace APSUniformization

open Nat
open APSMinimalInterface
open APSRecComp

/-! ## A1: Representable second projection -/

/-- Second projection: n ↦ (unpair n).2 -/
def HasRepresentableSnd (aps : IndexedAPS) : Prop :=
  IndexedRepresentableUnary aps (fun n => (unpair n).2)

/-- **Unshift lemma:** If second projection is representable, then for m = pair(x₀,n),
    we can extract n via (unpair m).2. So the "pairing shift" can be reversed
    at the input level. -/
theorem snd_extracts_from_pair (x₀ n : ℕ) :
    (unpair (pair x₀ n)).2 = n := by
  simp only [unpair_pair]

/-- **Section from I_comp + constants:** When const_e is representable,
    I_comp gives section surjectivity at every x₀. (Snd is not needed.) -/
theorem I_comp_constants_section (aps : IndexedAPS)
    (h_comp : HasICompIndexed aps) (e x₀ : ℕ)
    (h_const : IndexedRepresentableUnary aps (fun _ => e)) :
    ∃ k, ∀ n, aps.φ (aps.smn k x₀) n = aps.φ e n :=
  I_comp_implies_section_surj aps h_comp x₀ e h_const

/-- **Snd + comp ⇒ section:** With representable snd, the "unshift" is available.
    But composing e with snd to get m ↦ φ_e((unpair m).2) still requires I_comp. -/
theorem snd_comp_section (aps : IndexedAPS)
    (_h_snd : HasRepresentableSnd aps) (h_comp : HasICompIndexed aps) (e x₀ : ℕ)
    (h_const : IndexedRepresentableUnary aps (fun _ => e)) :
    ∃ k, ∀ n, aps.φ (aps.smn k x₀) n = aps.φ e n :=
  I_comp_constants_section aps h_comp e x₀ h_const

/-! ## A2: Fixed-point encoding attempt -/

/-- **Section requirement as fixed-point:** We want k with φ_k(pair(x₀,n)) = φ_e(n).
    Suppose we define h(k) = an index for the function m ↦ φ_e((unpair m).2) when
    (unpair m).1 = x₀. A fixed point k would satisfy φ_k = φ_{h(k)}. If h(k)
    computes m ↦ φ_e((unpair m).2) on the slice {pair(x₀,n) | n}, then
    φ_k(pair(x₀,n)) = φ_e(n). So k would be our section witness!
    The catch: h(k) requires composing e with snd and restricting to the slice.
    The composition needs I_comp. -/
def SectionAsFixedPoint (aps : IndexedAPS) (e x₀ : ℕ) : Prop :=
  ∃ (h : ℕ → ℕ),
    IndexedRepresentableUnary aps (fun x => h (aps.smn x x)) ∧
    (∀ k, (∀ n, aps.φ k n = aps.φ (h k) n) →
      ∀ n, aps.φ (aps.smn k x₀) n = aps.φ e n)

/-! ## A3: I_rec ⇒ HasGluing -/

/-- **Gluing from recursion:** HasGluing says finite trackers extend to global.
    I_rec gives fixed points. Can we use a fixed point whose "family" is the
    glued tracker? The gap: fixed points give smn(e,·) ≃ smn(h(e),·) at ONE e.
    Gluing needs a single k with smn(k,x) ≃ h₀(x) for ALL x. -/
theorem gluing_from_recursion_structure (aps : IndexedAPS)
    (_h_rec : HasIRecIndexed aps) (_h₀ : ℕ → ℕ)
    (_h₀_rep : IndexedRepresentableUnary aps _h₀)
    (_F : Finset ℕ) (_h_ft : ∃ k, ∀ x ∈ _F, ∀ n, aps.φ (aps.smn k x) n = aps.φ (_h₀ x) n) :
    True := trivial

end APSUniformization
