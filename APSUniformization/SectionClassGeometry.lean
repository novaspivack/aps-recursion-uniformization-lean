import APSUniformization.CloneDictionary
import APSUniformization.TrackerFailureRel
import APSRecComp
import APSMinimalInterface.Indexed

/-!
# Section Class Geometry — SPEC_V4 Workstream U1

The extensional section map σ_k(x) := [smn(k,x)] is the core object of uniformization theory.
We work with representative indices; extensional equality is ExtEq.

## Target U1

Define section extensional class maps σ_k(x) := [smn(k,x)] and prove all basic
invariance and compatibility laws.

## Key definitions

- `SectionClassAt aps k x` := aps.smn k x (the section index; its extensional class is [smn(k,x)])
- `TargetClassAt aps h₀ x` := h₀ x (the target index; its extensional class is [h₀(x)])
- Failure: x ∈ F_k ↔ σ_k(x) ≄ τ(x) ↔ ¬ExtEq (SectionClassAt ...) (TargetClassAt ...)
-/

namespace APSUniformization

open Nat
open Classical
open APSMinimalInterface
open APSRecComp

/-! ## Section class maps (Target U1) -/

/-- **Section class at x:** The index smn(k,x). Its extensional class [smn(k,x)]
    is the equivalence class under ExtEq. We use the index as representative. -/
def SectionClassAt (aps : IndexedAPS) (k x : ℕ) : ℕ :=
  aps.smn k x

/-- **Target class at x:** The index h₀(x). Its extensional class [h₀(x)] is
    the equivalence class under ExtEq. -/
def TargetClassAt (_aps : IndexedAPS) (h₀ : ℕ → ℕ) (x : ℕ) : ℕ :=
  h₀ x

/-- **Section matches target at x:** σ_k(x) ≃ τ(x), i.e. ExtEq (smn k x) (h₀ x). -/
def SectionMatchesTargetAt (aps : IndexedAPS) (h₀ : ℕ → ℕ) (k x : ℕ) : Prop :=
  ExtEq aps (SectionClassAt aps k x) (TargetClassAt aps h₀ x)

/-- **Section matches target ↔ no tracker failure.** -/
theorem section_matches_target_iff_no_failure (aps : IndexedAPS) (h₀ : ℕ → ℕ) (k x : ℕ) :
    SectionMatchesTargetAt aps h₀ k x ↔ ¬ TrackerFailureRel aps h₀ k x := by
  simp only [SectionMatchesTargetAt, SectionClassAt, TargetClassAt, ExtEq]
  simp only [TrackerFailureRel]
  push_neg
  rfl

/-! ## Invariance and compatibility laws (Target U1) -/

/-- **U1.1 — Section class is determined by smn:** SectionClassAt aps k x = aps.smn k x. -/
theorem section_class_at_eq_smn (aps : IndexedAPS) (k x : ℕ) :
    SectionClassAt aps k x = aps.smn k x := rfl

/-- **U1.2 — Extensional invariance of section class:** If smn(k,x) ≃ smn(k',x'),
    then SectionMatchesTargetAt agrees for both at their respective targets when
    the targets agree extensionally. -/
theorem section_class_extensional_invariance (aps : IndexedAPS) (h₀ : ℕ → ℕ) (k k' x x' : ℕ)
    (hsec : ∀ n, aps.φ (aps.smn k x) n = aps.φ (aps.smn k' x') n)
    (htarg : ∀ n, aps.φ (h₀ x) n = aps.φ (h₀ x') n) :
    SectionMatchesTargetAt aps h₀ k x ↔ SectionMatchesTargetAt aps h₀ k' x' := by
  simp only [SectionMatchesTargetAt, SectionClassAt, TargetClassAt, ExtEq]
  constructor
  · intro h n
    rw [← hsec n, ← htarg n]
    exact h n
  · intro h n
    rw [hsec n, htarg n]
    exact h n

/-- **U1.3 — Same section ⇒ same match:** When k₁ and k₂ have same section at x,
    SectionMatchesTargetAt aps h₀ k₁ x ↔ SectionMatchesTargetAt aps h₀ k₂ x. -/
theorem section_match_same_section (aps : IndexedAPS) (h₀ : ℕ → ℕ) (k₁ k₂ x : ℕ)
    (hsec : ∀ n, aps.φ (aps.smn k₁ x) n = aps.φ (aps.smn k₂ x) n) :
    SectionMatchesTargetAt aps h₀ k₁ x ↔ SectionMatchesTargetAt aps h₀ k₂ x :=
  section_class_extensional_invariance aps h₀ k₁ k₂ x x hsec (fun _ => rfl)

/-- **U1.4 — Same target and same section ⇒ same match:** When h₀(x) ≃ h₀(x')
    and smn(k,x) ≃ smn(k,x'), SectionMatchesTargetAt agrees. (Without same section,
    the theorem fails: the section at x can differ from the section at x'.) -/
theorem section_match_same_target_and_section (aps : IndexedAPS) (h₀ : ℕ → ℕ) (k x x' : ℕ)
    (hsec : ∀ n, aps.φ (aps.smn k x) n = aps.φ (aps.smn k x') n)
    (htarg : ∀ n, aps.φ (h₀ x) n = aps.φ (h₀ x') n) :
    SectionMatchesTargetAt aps h₀ k x ↔ SectionMatchesTargetAt aps h₀ k x' :=
  section_class_extensional_invariance aps h₀ k k x x' hsec htarg

/-- **U1.5 — Failure set as inverse image:** F_k = {x : σ_k(x) ≄ τ(x)}.
    This is the characterization from SPEC_V4 Target U2. -/
theorem failure_set_as_inverse_image (aps : IndexedAPS) (h₀ : ℕ → ℕ) (k x : ℕ) :
    x ∈ TrackerFailureSet aps h₀ k ↔ ¬ SectionMatchesTargetAt aps h₀ k x := by
  simp only [TrackerFailureSet, Set.mem_setOf_eq]
  rw [section_matches_target_iff_no_failure]
  exact not_not.symm

/-- **U1.6 — Compatibility with tracker_failure_extensional:** Our invariance
    laws imply the Option 8 extensionality theorem. -/
theorem section_class_implies_tracker_failure_extensional (aps : IndexedAPS) (h₀ : ℕ → ℕ)
    (k k' x x' : ℕ)
    (hkk' : ∀ n, aps.φ (aps.smn k x) n = aps.φ (aps.smn k' x') n)
    (hxx' : ∀ n, aps.φ (h₀ x) n = aps.φ (h₀ x') n) :
    TrackerFailureRel aps h₀ k x ↔ TrackerFailureRel aps h₀ k' x' :=
  tracker_failure_extensional aps h₀ k k' x x' hkk' hxx'

/-- **U1.7 — Reflexivity of ExtEq for section class:** SectionClassAt aps k x ≃ SectionClassAt aps k x. -/
theorem section_class_reflexive (aps : IndexedAPS) (k x : ℕ) :
    ExtEq aps (SectionClassAt aps k x) (SectionClassAt aps k x) := fun _ => rfl

/-- **U1.8 — Section class from APS:** Every σ_k arises from some IndexedAPS.
    (Trivial: we defined it from aps.) The nontrivial question is which *families*
    of maps σ_k can arise; that is Workstream U5 (counterexample templates). -/
theorem section_class_arises_from_aps (aps : IndexedAPS) (k x : ℕ) :
    SectionClassAt aps k x = aps.smn k x := rfl

end APSUniformization
