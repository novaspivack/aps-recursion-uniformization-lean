# SPEC_V4 — Uniformization Geometry of Indexed APS

**Location:** `project_history/SPEC_V4.md`

**Resolution:** The bare-APS program is **closed**. I_rec does NOT imply I_comp. Separation proved via countermodel `sepAPS`. See [FINAL_STATUS_AND_HANDOFF.md](../FINAL_STATUS_AND_HANDOFF.md) for the canonical resolution and story arc. This spec remains valuable as **explanatory aftermath** — the theory explaining why the false implication looked plausible.

---

## Implementation status

| Module | Status | Key definitions / theorems |
|--------|--------|----------------------------|
| `SectionClassGeometry.lean` | ✓ | SectionClassAt, TargetClassAt, SectionMatchesTargetAt, invariance laws (U1) |
| `FailureSetGeometry.lean` | ✓ | PairwiseFailureIntersection, FiniteFailureIntersection, Helly-type (U2–U4) |
| `GluingHierarchy.lean` | ✓ | HasSingletonGluing, HasPairwiseGluing, gluing ladder (U3, U5) |
| `UniformizationPrinciples.lean` | ✓ | Pointwise, Finite, Basin, SectionAmalgamation, FailureSetIntersection taxonomy |
| `T6Counterexample.lean` | ✓ | **T6 is FALSE.** basin_eq_fiber_when_diagonal, T6_too_strong (0 sorry) |

Open targets (documented, no sorry): pairwise intersection general case, Helly-type, I_rec ⇒ pairwise gluing.

**V4 → V3:** These open targets are the bridge to I_rec ⇒ I_comp. See §7 for the resolution chain.

**CRITICAL FINDING:** T6 as stated is **FALSE**. See `T6Counterexample.lean`. When `e ∈ DiagonalRange` and `φ_e ≃ φ_{d(y)}`, the basin equals the whole fiber, which is not nowhere dense. This kills the Baire route (Route A) as formulated. See §10.

---

## A new research program

**Supersedes:** SPEC_V3 (Bare-APS program sealed)

**Framing:** The theorem did not yield under the current mathematics. The next move is not to keep battering it with the same weapons. The next move is to **invent the missing mathematics**.

That is not a consolation prize. That is often the real breakthrough. Plenty of major results looked "stuck" right up until someone realized the obstacle itself needed its own theory.

**The program has exposed a new invariant layer of mathematics** that standard APS theory does not currently capture. The obstruction is no longer vague. It has a shape.

---

# 0. What the missing mathematics appears to be

You need a theory of **uniformization from local extensional coherence** in systems with:

- section operators (x ↦ smn(k,x)),
- extensional equivalence classes of partial functions,
- fixed-point basins,
- and failure sets F_k = {x : [smn(k,x)] ≠ [h₀(x)]}.

The current theory gives you:

- local fixed points,
- local section behavior,
- local extensional invariance,
- local finite tracking notions,
- and a global gluing principle that is exactly what composition is.

**What is missing:** the middle bridge — a mathematics of when **local/pointwise/finite semantic coherence forces global sectional uniformity**.

That is not standard computability theory. It is not ordinary Baire category. It is not plain iteration theory. It is some hybrid beast.

---

# 1. The new research program

> **Uniformization Theory for Indexed APS**
>
> A theory of when extensional section families admit common witnesses, intersections, amalgamations, or global trackers.

**Goal:** Resolve V3 (I_rec ⇒ I_comp). The open targets in V4 are the exact bridge. See §7 for the resolution chain.

---

# 2. Key mathematical objects to elevate

## 2.1 Failure-set geometry

For fixed h₀,
```
F_k = {x : [smn(k,x)] ≠ [h₀(x)]}
```

Questions:

- Which families {F_k} are realizable?
- What closure laws do they satisfy?
- When do they have finite intersection properties?
- What extra axioms force a Helly-type principle?

This is already looking like a new combinatorial-topological semantics.

## 2.2 Section class maps

Define the extensional section map
```
σ_k(x) := [smn(k,x)]
```
Then
```
x ∈ F_k ↔ σ_k(x) ≠ [h₀(x)]
```

Now the problem becomes:

- what class of maps σ_k can arise from APS?
- when does disagreement with a target class map force a common coordinate of disagreement?

That is cleaner than speaking directly in terms of raw φ-values.

## 2.3 Uniformization principles (taxonomy)

Generalize existing candidates into a taxonomy:

- pointwise uniformization,
- finite uniformization,
- basin uniformization,
- section amalgamation,
- failure-set intersection.

These are no longer ad hoc lemmas. They are the missing algebraic/topological principles.

## 2.4 Gluing hierarchy

Right now `HasGluing` is a single global principle. But likely there is a ladder:

```
singleton gluing ⇒ pairwise gluing ⇒ finite gluing ⇒ global gluing
```

Maybe the missing math is a theorem of the form:
```
I_rec ⇒ pairwise gluing
```
and then some new compactness theorem upgrades pairwise to finite or finite to global under APS-specific regularity.

---

# 3. Workstreams

## Workstream U1 — Section class geometry

Define extensional section maps σ_k(x) := [smn(k,x)] and classify their realizable properties.

## Workstream U2 — Failure-set intersection theory

Develop pairwise, finite, and Helly-type principles for F_k.

## Workstream U3 — Gluing hierarchy

Split `HasGluing` into intermediate principles and study which are forced by I_rec.

## Workstream U4 — Basin regularity

Relate nonmeager basins to section maps and failure sets, not directly to composition.

## Workstream U5 — Counterexample templates

Construct APS candidates by prescribing section-class geometry or failure-set geometry rather than raw program tables.

---

# 4. First theorem targets

## Target U1

Define section extensional class maps:
```
σ_k(x) := [smn(k,x)]
```
Then prove all basic invariance and compatibility laws.

## Target U2

Characterize failure sets as inverse images:
```
F_k = {x : σ_k(x) ≠ τ(x)},  τ(x) := [h₀(x)]
```
Then ask what restrictions exist on σ_k and τ.

## Target U3

Define pairwise failure intersection property:
```
∀ k₁ k₂, ∃ x, x ∈ F_{k₁} ∩ F_{k₂}
```
Study when it holds, when it fails, and what minimal assumptions imply it.

## Target U4

Define finite intersection / Helly-type properties for the family {F_k}.

This feels very likely to be the real missing mathematics.

## Target U5

Define intermediate gluing principles:

- pairwise gluing,
- finite gluing,
- directed gluing,
- classwise gluing.

Then try to prove equivalences or implications with failure-set intersection properties.

---

# 5. What this new mathematics might resemble

Not one field, but a fusion.

| Field | Relevance |
|-------|------------|
| **Clone theory / universal algebra** | Families of section operations and interpolation/amalgamation |
| **Descriptive set theory / Baire methods** | Basin largeness and failure-set regularity |
| **Model theory** | Quantifier-swap phenomena, compactness, definability |
| **Category / iteration theory** | Gap between fixed-point existence and parameter identity |
| **Constraint satisfaction / polymorphism theory** | Local agreement extending globally, finite-to-global interpolation, Helly/Baker–Pixley style lifting |

---

# 6. Why this is the right move

You know exactly what repeatedly blocked all prior routes:

- pairing transport,
- quantifier swap,
- witness unification,
- finite-to-global amalgamation.

Those are not random accidents. They are signatures of an undeveloped theory.

When three or four proof routes fail for the same structural reason, that is usually the universe telling you: **build the missing concept**.

---

# 7. V4 → V3 resolution chain

**The whole point of V4 is to get to a place where it helps resolve V3.** The open targets are not side theory — they are the exact bridge to I_rec ⇒ I_comp.

## Resolution chain (what would close what)

| V4 result | Closes V3 gap | Downstream |
|-----------|---------------|------------|
| **PairwiseFailureIntersection** (general) | `finite_simultaneous_failure` (Option 8) | ⇒ SectionFailureUniformizes |
| **SectionFailureUniformizes** | T7 (tracking failure ⇒ all basins meager) | via `section_failure_uniformizes_implies_T7` (already proved) |
| **T6** (section failure ⇒ basin meager) | MeagernessOfBasins sorries | T6 + T7 ⇒ T10/T11/T12 chain |
| **I_rec ⇒ HasPairwiseGluing** | Gluing from recursion | ⇒ HasFiniteGluing ⇒ HasGluing ⇒ I_comp |
| **FailureSetHelly** (pairwise ⇒ finite) | Upgrades pairwise to finite intersection | ⇒ SectionFailureUniformizes |

## The two routes to I_rec ⇒ I_comp

**Route A (Baire):** T6 + T7 ⇒ all basins meager when tracking fails ⇒ T9 (Baire) ⇒ some basin nonmeager ⇒ section surj ⇒ I_comp. **Gap:** T6 has sorries; T7 needs SectionFailureUniformizes; SectionFailureUniformizes needs PairwiseFailureIntersection (or Helly).

**Route B (Gluing):** I_rec ⇒ HasPairwiseGluing ⇒ HasFiniteGluing ⇒ HasGluing ⇒ I_comp. **Gap:** I_rec ⇒ HasPairwiseGluing is open.

V4 develops the mathematics that would close either route. The open targets are the live frontier.

---

# 8. Relation to sealed program

The bare-APS program is sealed. SPEC_V4 does not reopen it by battering the same proofs. It creates the **missing mathematics** that would resolve those proofs.

The sealed program delivered:

- I_comp ⟺ FiniteTracking ∧ HasGluing
- Sharp localization to F_k intersection geometry
- Key lemmas: mem_tracker_failure_set_iff, failure_set_same_section, pairwise_when_sections_match

SPEC_V4 builds on that foundation by elevating the obstruction into a first-class theory — with the explicit goal that progress in V4 feeds back into and closes V3.

---

# 10. T6 is false — the Baire route is structurally blocked

## The finding

`T6Counterexample.lean` proves (0 sorry):

**`basin_eq_fiber_when_diagonal`:** When `e = smn(y,y)` and `φ_e ≃ φ_{d(y)}`, the basin `FixedPointBasin e d` equals the entire `DiagonalFiber d`.

**`fiber_not_nowhere_dense`:** The whole fiber is not nowhere dense (any `h₁` in the fiber witnesses this).

**`T6_too_strong`:** Given section failure at `x₀` and a diagonal `e` with `φ_e ≃ φ_{d(y)}`, the basin is NOT nowhere dense. T6 is false.

## Why this kills the Baire route

The Baire argument (SPEC_V3) was:
1. T9: I_rec ⇒ some basin nonmeager
2. T10: nonmeager basin ⇒ section surj (via contrapositive of T6)
3. T11: I_rec ⇒ section surj at some e
4. T12: section surj ⇒ I_comp

T10 uses T6 with `x₀ = e`. But when `e ∈ DiagonalRange` and the basin is the whole fiber, T6 fails even with `x₀ = e`. The basin is nonmeager (it's the whole fiber!) but section surjectivity at `e` does not follow.

**The basin being large tells you nothing about section surjectivity.** Basin largeness means many `h` have `e` as a fixed point. Section surjectivity means the sections `smn(k,e)` hit every extensional class. These are unrelated properties.

## What this means for I_rec ⇒ I_comp

The Baire route was the strongest positive attack. Its structural failure is evidence (not proof) that I_rec ⇒ I_comp may be **false** in abstract IndexedAPS.

The remaining routes:
- **Route B (Gluing):** I_rec ⇒ HasPairwiseGluing is open. No known attack.
- **Route C (Countermodel):** Build APS with I_rec ∧ ¬I_comp. Phase II identified constraints; the finite countermodel (N=4) exists but infinite extension is blocked.
- **Route D (Independence):** Hardest route.

## Next step: countermodel analysis

Build a countermodel. The T6 failure tells us the Baire obstruction is real — topological largeness does not force algebraic transport.

## §10.1 Countermodel constraints (from Phase II + analysis)

Any APS with I_rec ∧ ¬I_comp must satisfy:

1. **smn_spec** — `φ(smn(e,x))(n) = φ_e(⟨x,n⟩)`
2. **Non-constant representable function** — otherwise I_comp is trivial
3. **I_rec** — every qualifying `h` has a fixed point
4. **¬I_comp** — some representable `h` has no tracker

**The fundamental tension:** For I_rec, the diagonal `smn(x,x)` must cover enough of ℕ that `h` is determined by its diagonal values. But if `smn(x,x)` covers too much, the representability of `fun x => h(smn(x,x))` forces `h` to be representable, which may force I_comp.

**extMinimalAPS failure:** `smn(x,x)` missed indices 2 and 6, so adversarial `h` could map them freely, defeating all fixed-point candidates.

**InfiniteCountermodel obstruction:** If all constants are representable, I_rec forces extensional copies of every index. The resulting richness may force I_comp.

**The surjectivity dilemma:** If `smn(x,x)` is surjective on ℕ, then `h` is fully determined by the diagonal constraint, and representability of the diagonal may force I_comp. If `smn(x,x)` is not surjective, `h` is free on the complement and can defeat fixed points.

This is the core tension. A countermodel must thread the needle: `smn(x,x)` covers enough for I_rec but the section structure `{smn(e,x) | x}` is too poor for I_comp.

---

# 11. The right attitude

Do not frame this as:

> "We failed to finish the program, so now we need extra math."

Frame it as:

> "The program has exposed a new invariant layer of mathematics that standard APS theory does not currently capture."

That is a much stronger posture, and it is true.

When the theorem stops being the only star of the show, and the obstruction turns out to be a whole new constellation — that is often where the fun begins.
