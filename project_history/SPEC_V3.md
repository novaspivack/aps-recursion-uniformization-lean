# Phase III Research Spec v3

**Location:** `project_history/SPEC_V3.md`

**Resolution:** The bare-APS program is **closed**. I_rec does NOT imply I_comp. Separation proved via countermodel `sepAPS`. See [FINAL_STATUS_AND_HANDOFF.md](../FINAL_STATUS_AND_HANDOFF.md) for the canonical resolution.

---

## Baire-Category / Descriptive-Set-Theoretic Attack

### Target: close the recursion–composition frontier via topological size arguments on function spaces

**Supersedes:** SPEC_V2.md (clone/interpolation/iteration/countermodel program)

**Status of SPEC_V2 program (historical):**
- Outcome B (algebraic exactness): **DONE** — I_comp ⟺ FiniteTracking ∧ Gluing
- Outcome A (conditional positive): **DONE** — I_rec + JointSectionSurj + Gluing ⇒ I_comp
- Outcome C (countermodel): **ACHIEVED** — sepAPS (not extMinimalAPS)
- Outcome D (independence): **N/A** — implication is false, not independent
- **The gap I_rec ⇒ I_comp is RESOLVED (false)**

---

# 0. The new diagnosis

The SPEC_V2 methods are exhausted. The countermodel route is blocked by the smn_spec entanglement (documented in Phase II `RecursionCountermodelSearch.lean`). The direct algebraic route is blocked by the second-order gap: I_rec controls "what e computes" but not "how e curries" (documented in `DiagonalReflection.lean`).

The existing Phase II/III infrastructure has already built the key ingredients for a Baire-category argument without recognizing it as such:

- `DiagonalRange` and `DiagonalFiber` structure (Phase II `CardinalityArgument.lean`)
- Continuum-many h-functions per diagonal, countably many candidate fixed points (Phase II `CardinalityProof.lean`)
- `shared_fp_forces_agreement`: fixed points are over-determined (Phase II `CardinalityArgument.lean`)
- `off_diagonal_fp_obstruction`: off-diagonal universal fixed points force extensional collapse (Phase II `CardinalityProof.lean`)
- The reflection theorem: I_rec + I_diag gives a self-referential tracker structure (Phase II `DiagonalReflection.lean`)

**The new insight:** The cardinality heuristic is a Baire-category argument in disguise. Formalizing it as such is the most promising route to closing the gap.

---

# 1. The mathematical strategy

## The function space

Fix a representable diagonal `d : ℕ → ℕ` (the common value of `h(smn x x)`). Define:

```
DiagonalFiber d := { h : ℕ → ℕ | ∀ x, h (smn x x) = d x }
```

This is the space of all qualifying h-functions for a given diagonal. It is naturally a product space (h is free off the diagonal range), homeomorphic to `ℕ^(ℕ \ DiagonalRange)` with the product topology — a Baire space.

## The fixed-point basins

For each index `e`, define:

```
FixedPointBasin e d := { h ∈ DiagonalFiber d | φ_e = φ_{h(e)} }
```

If I_rec holds, then for every qualifying diagonal d:

```
DiagonalFiber d = ⋃_{e : ℕ} FixedPointBasin e d
```

## The Baire argument

**If** each `FixedPointBasin e d` is meager (nowhere dense in the product topology), then by the Baire category theorem their countable union cannot cover `DiagonalFiber d`. This contradicts I_rec.

Therefore: **if I_rec holds, some `FixedPointBasin e d` must be nonmeager (comeager on some open set).**

**The claim:** nonmeagerness of `FixedPointBasin e d` forces section surjectivity or tracking at e.

If this claim holds, the chain closes: I_rec ⇒ some large basin ⇒ section surjectivity ⇒ finite tracking ⇒ (+ gluing) I_comp.

---

# 2. Why this is the right tool

The existing cardinality argument (Phase II) already shows:
- Continuum-many h-functions share countably many fixed points
- Shared fixed points force extensional agreement at those indices
- Off-diagonal universal fixed points force collapse

The Baire-category formulation makes this precise:
- "Continuum-many h-functions" = the fiber is uncountable / Baire
- "Countably many fixed points" = countably many basins
- "Cannot cover" = Baire category theorem
- "Some basin is large" = some basin is nonmeager
- "Large basin forces tracking" = the new theorem to prove

This is not a new idea from outside — it is the natural completion of the existing cardinality heuristic.

---

# 3. Module plan

## New modules for this repo (`APSUniformization/`)

### `BaireSpaceOfDiagonals.lean`
Formalize the function space structure.

**Definitions:**
```lean
def DiagonalFiber (aps : IndexedAPS) (d : ℕ → ℕ) : Set (ℕ → ℕ) :=
  { h | ∀ x, h (aps.smn x x) = d x }

-- Cylinder sets: h agrees with h₀ on a finite set F ⊆ ℕ \ DiagonalRange
def CylinderSet (aps : IndexedAPS) (h₀ : ℕ → ℕ) (F : Finset ℕ)
    (hF : ∀ x ∈ F, x ∉ DiagonalRange aps) : Set (ℕ → ℕ) :=
  { h | ∀ x ∈ F, h x = h₀ x }

-- A set S ⊆ DiagonalFiber d is dense if every cylinder meets S
def DenseInFiber (aps : IndexedAPS) (d : ℕ → ℕ) (S : Set (ℕ → ℕ)) : Prop :=
  ∀ (h₀ : ℕ → ℕ) (F : Finset ℕ), (∀ x ∈ F, x ∉ DiagonalRange aps) →
    ∃ h ∈ S ∩ DiagonalFiber aps d, ∀ x ∈ F, h x = h₀ x

-- A set is nowhere dense if its closure has empty interior (no cylinder inside)
def NowhereDenseInFiber (aps : IndexedAPS) (d : ℕ → ℕ) (S : Set (ℕ → ℕ)) : Prop :=
  ∀ (h₀ : ℕ → ℕ) (F : Finset ℕ), (∀ x ∈ F, x ∉ DiagonalRange aps) →
    ∃ (G : Finset ℕ), F ⊆ G ∧ (∀ x ∈ G \ F, x ∉ DiagonalRange aps) ∧
      ∀ h ∈ DiagonalFiber aps d, (∀ x ∈ G, h x = h₀ x) → h ∉ S

-- Meager = countable union of nowhere dense sets
def MeagerInFiber (aps : IndexedAPS) (d : ℕ → ℕ) (S : Set (ℕ → ℕ)) : Prop :=
  ∃ (Sn : ℕ → Set (ℕ → ℕ)), S ⊆ ⋃ n, Sn n ∧ ∀ n, NowhereDenseInFiber aps d (Sn n)
```

**Theorem targets:**
```lean
-- T0. The fiber is a Baire space: countable intersections of dense open sets are dense
theorem diagonal_fiber_baire (aps : IndexedAPS) (d : ℕ → ℕ) :
    BaireSpaceProperty (DiagonalFiber aps d)

-- T0'. Countable union of meager sets cannot cover the fiber
theorem meager_union_does_not_cover (aps : IndexedAPS) (d : ℕ → ℕ)
    (S : ℕ → Set (ℕ → ℕ)) (hS : ∀ n, MeagerInFiber aps d (S n)) :
    ∃ h ∈ DiagonalFiber aps d, ∀ n, h ∉ S n
```

---

### `FixedPointBasins.lean`
Characterize the fixed-point basins.

**Definitions:**
```lean
def FixedPointBasin (aps : IndexedAPS) (e : ℕ) (d : ℕ → ℕ) : Set (ℕ → ℕ) :=
  { h ∈ DiagonalFiber aps d | ∀ n, aps.φ e n = aps.φ (h e) n }
```

**Theorem targets:**
```lean
-- T1. I_rec ⇒ basins cover the fiber
theorem I_rec_implies_basins_cover (aps : IndexedAPS)
    (h_rec : HasIRecIndexed aps) (d : ℕ → ℕ)
    (hd_rep : IndexedRepresentableUnary aps d) :
    DiagonalFiber aps d ⊆ ⋃ e, FixedPointBasin aps e d

-- T2. Basin characterization: h ∈ FixedPointBasin e d iff h(e) ≃ e (extensionally)
theorem basin_characterization (aps : IndexedAPS) (e : ℕ) (d : ℕ → ℕ) (h : ℕ → ℕ) :
    h ∈ FixedPointBasin aps e d ↔
    h ∈ DiagonalFiber aps d ∧ ∀ n, aps.φ e n = aps.φ (h e) n

-- T3. Basin is determined by the extensional class of h(e)
-- All h ∈ FixedPointBasin e d must map e to an index extensionally equal to e
theorem basin_ext_constraint (aps : IndexedAPS) (e : ℕ) (d : ℕ → ℕ)
    (h₁ h₂ : ℕ → ℕ) (h₁_in : h₁ ∈ FixedPointBasin aps e d)
    (h₂_in : h₂ ∈ FixedPointBasin aps e d) :
    ∀ n, aps.φ (h₁ e) n = aps.φ (h₂ e) n

-- T4. If e ∈ DiagonalRange, the basin is a cylinder set (closed, not nowhere dense)
theorem basin_diagonal_is_cylinder (aps : IndexedAPS) (e : ℕ) (d : ℕ → ℕ)
    (he : e ∈ DiagonalRange aps) :
    ∃ (F : Finset ℕ) (h₀ : ℕ → ℕ),
      FixedPointBasin aps e d = CylinderSet aps h₀ F (by sorry) ∩ DiagonalFiber aps d

-- T5. If e ∉ DiagonalRange, the basin is a "thin" set
-- (h is free to choose h(e) from the extensional class of e, but this is a single constraint)
theorem basin_off_diagonal_thin (aps : IndexedAPS) (e : ℕ) (d : ℕ → ℕ)
    (he : e ∉ DiagonalRange aps) :
    NowhereDenseInFiber aps d (FixedPointBasin aps e d) ∨
    (∃ c, ∀ h ∈ FixedPointBasin aps e d, ∀ n, aps.φ (h e) n = aps.φ c n)
```

---

### `MeagernessOfBasins.lean`
The core meagerness analysis.

**Theorem targets:**
```lean
-- T6. If section surjectivity fails at x₀, then FixedPointBasin e d is meager
-- for every e that is a "section-deficient" index
theorem section_failure_implies_meager_basin (aps : IndexedAPS) (x₀ e : ℕ) (d : ℕ → ℕ)
    (h_fail : ¬ SmnSectionSurjectiveAt aps x₀) :
    NowhereDenseInFiber aps d (FixedPointBasin aps e d)

-- T7. If tracking fails for h₀, then the basin for any tracker candidate is meager
theorem tracking_failure_implies_meager_basins (aps : IndexedAPS) (h₀ : ℕ → ℕ) (d : ℕ → ℕ)
    (h_ntrack : ¬ SmnReachable aps h₀) :
    ∀ e, NowhereDenseInFiber aps d (FixedPointBasin aps e d)

-- T8. If all basins are meager, the fiber cannot be covered (Baire)
theorem all_meager_not_covered (aps : IndexedAPS) (d : ℕ → ℕ)
    (hm : ∀ e, MeagerInFiber aps d (FixedPointBasin aps e d)) :
    ∃ h ∈ DiagonalFiber aps d, ∀ e, h ∉ FixedPointBasin aps e d
```

---

### `BaireCoverArgument.lean`
The main argument connecting Baire to I_rec.

**Theorem targets:**
```lean
-- T9. I_rec ⇒ some basin is nonmeager
theorem I_rec_implies_nonmeager_basin (aps : IndexedAPS)
    (h_rec : HasIRecIndexed aps) (d : ℕ → ℕ)
    (hd_rep : IndexedRepresentableUnary aps d) :
    ∃ e, ¬ MeagerInFiber aps d (FixedPointBasin aps e d)

-- T10. Nonmeager basin ⇒ section surjectivity (the key new theorem)
theorem nonmeager_basin_implies_section_surj (aps : IndexedAPS) (e : ℕ) (d : ℕ → ℕ)
    (h_nonmeager : ¬ MeagerInFiber aps d (FixedPointBasin aps e d)) :
    SmnSectionSurjectiveAt aps e

-- T11. Combining: I_rec ⇒ SmnSectionSurjectiveAt (conditional on T10)
theorem I_rec_implies_section_surj (aps : IndexedAPS)
    (h_rec : HasIRecIndexed aps) (d : ℕ → ℕ)
    (hd_rep : IndexedRepresentableUnary aps d) :
    ∃ x₀, SmnSectionSurjectiveAt aps x₀
```

---

### `PositiveResolution.lean`
The final theorem, combining with the existing chain.

**Theorem targets:**
```lean
-- T12. I_rec + (Baire meagerness results) ⇒ I_comp
-- This is the summit theorem, conditional on T6/T7/T10
theorem I_rec_implies_I_comp_via_baire (aps : IndexedAPS)
    (h_rec : HasIRecIndexed aps)
    (h_diag : HasIDiagIndexed aps)
    (h_const : ∀ c, IndexedRepresentableUnary aps (fun _ => c))
    -- Key hypothesis: section failure implies meager basins
    (h_meager : ∀ x₀ e d, ¬ SmnSectionSurjectiveAt aps x₀ →
      NowhereDenseInFiber aps d (FixedPointBasin aps e d)) :
    HasICompIndexed aps
```

---

# 4. What is already available

The following infrastructure from Phase II/III is directly usable:

| Existing theorem | Where | Role in Baire argument |
|-----------------|-------|----------------------|
| `DiagonalRange` | Phase II `CardinalityArgument.lean` | Defines the constrained vs free coordinates |
| `shared_fp_forces_agreement` | Phase II `CardinalityArgument.lean` | Basin characterization (T3) |
| `off_diagonal_fp_obstruction` | Phase II `CardinalityProof.lean` | Off-diagonal basin thinness (T5) |
| `diag_reflect_has_fp` | Phase II `DiagonalReflection.lean` | I_rec ⇒ basins cover (T1) |
| `SmnSectionSurjectiveAt` | Phase II `SmnSectionSurjectivity.lean` | Target of T10/T11 |
| `section_surj_at_implies_singleton_tracking` | Phase II `SmnSectionSurjectivity.lean` | Chain to I_comp |
| `comp_iff_finite_tracking_and_gluing` | Phase III `Interpolation.lean` | Final step to I_comp |
| `I_comp_implies_section_surj` | Phase III `GapClosure.lean` | Converse direction |

---

# 5. The key open theorem (T10)

The hardest and most important new theorem is **T10**: nonmeager basin ⇒ section surjectivity.

**Intuition:** If `FixedPointBasin e d` is nonmeager, then it is "large" in the fiber — it contains h-functions in every open cylinder. This means: for every finite set F of off-diagonal indices and every assignment of values on F, there exists h ∈ basin with those values. In particular, for any target value c at index e, there exists h ∈ basin with h(e) ≃ c. Since h ∈ basin means φ_e = φ_{h(e)} ≃ φ_c, this forces φ_e ≃ φ_c for all c. But that collapses all extensional classes to e — contradiction unless the basin is "large" in a different sense.

**The correct version:** Nonmeagerness of the basin at e means the basin is dense on some open cylinder. This forces: for some fixed finite assignment on F, every extension to the rest of the fiber is in the basin. This means h(e) is forced to be extensionally equal to e for all such extensions. The forced value h(e) ≃ e is then a section witness: smn(e, x₀) ≃ e for appropriate x₀.

This argument needs to be made precise. It may require:
- A version of the Baire category theorem for the product topology on `ℕ^S` where S = ℕ \ DiagonalRange
- A density/regularity lemma connecting basin nonmeagerness to section surjectivity
- Possibly: the basin being nonmeager forces it to contain a "generic" h, and generic h forces the section structure

---

# 6. What if T10 fails?

If T10 cannot be proved, the failure is informative:

- It means a nonmeager basin can exist without forcing section surjectivity
- This gives a precise blueprint for a countermodel: an APS where some fixed-point basin is large but no section surjectivity holds
- The countermodel would need to have a "large" fixed-point basin that is "disconnected" from the section structure
- This is a more structured countermodel design than the extMinimalAPS attempt

So even failure of T10 advances the research.

---

# 7. Relationship to existing workstreams

**Clone theory (SPEC_V2 Workstream A):** Still relevant as a dictionary. The Baire argument uses the clone structure implicitly (section surjectivity = projection surjectivity in the clone).

**Interpolation (SPEC_V2 Workstream B):** The chain FiniteTracking + Gluing ⇒ I_comp is already proved. The Baire argument feeds into this chain via section surjectivity.

**Iteration theory (SPEC_V2 Workstream C):** Remains as conceptual context. The parameter identity gap is the same gap the Baire argument addresses.

**Countermodel (SPEC_V2 Workstream D):** The Baire argument, if it fails, gives a better countermodel blueprint than the extMinimalAPS approach.

---

# 8. Priority order

1. **First:** Formalize `BaireSpaceOfDiagonals.lean` — the topological setup. This is purely definitional and does not require new mathematical insight.

2. **Second:** Formalize `FixedPointBasins.lean` — characterize the basins using existing Phase II results. T1, T2, T3 are straightforward from existing infrastructure.

3. **Third:** Attempt T10 — nonmeager basin ⇒ section surjectivity. This is the key new theorem. If it works, the summit is in reach. If it fails, the failure analysis gives a countermodel blueprint.

4. **Fourth:** If T10 works, complete `BaireCoverArgument.lean` and `PositiveResolution.lean`.

---

# 9. Acceptance criteria

## Strong success (closes the gap)
- T10 proved: nonmeager basin ⇒ section surjectivity
- T9 proved: I_rec ⇒ some basin nonmeager
- T12 proved: I_rec ⇒ I_comp (possibly with mild regularity hypotheses)

## Medium success (major advance)
- T1–T5 proved: full characterization of fixed-point basins
- T6/T7 proved: section/tracking failure ⇒ meager basins
- T9 proved: I_rec ⇒ some basin nonmeager
- T10 attempted with precise statement of what is needed

## Weak success (structural advance)
- `BaireSpaceOfDiagonals.lean` and `FixedPointBasins.lean` formalized
- T10 precisely stated as the key open theorem
- Failure analysis of T10 gives countermodel blueprint

---

# 10. One-sentence mission

> Prove that if I_rec holds, some fixed-point basin in the diagonal fiber is nonmeager, and that nonmeagerness forces section surjectivity — closing the recursion–composition gap via Baire category.
