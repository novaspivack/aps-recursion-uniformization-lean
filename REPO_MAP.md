# Repository Map — APS Recursion Uniformization

## Where we are

This repo (**aps-recursion-uniformization-lean**) is **Phase III** of the APS interface program. It continues the attack on the recursion–composition frontier using clone theory, universal algebra, and iteration theory.

## Dependency chain

```
Phase I: aps-undecidability-interfaces-lean
    └── APSMinimalInterface (IndexedAPS, I_rec, I_comp, I_diag, minimalIndexedAPS, stdAPS, ...)

Phase II: aps-recursion-composition-uniformity-lean
    └── APSRecComp (corrected exactness, regime bifurcation, gap location, Phase III modules)
    └── depends on Phase I

Phase III: aps-recursion-uniformization-lean  ← YOU ARE HERE
    └── APSUniformization (clone semantics, interpolation, iteration translation)
    └── depends on Phase I and Phase II
```

## What Phase I established

- Total-tier exact minimality for diagonal closure
- Indexed interface taxonomy
- Indexed separation lattice
- Rice bifurcation, strong-Rice mechanism bifurcation
- Standard comparison
- Frontier theorem `comp_iff_smn_tracks`
- **Sufficiency:** I_comp + I_diag ⇒ I_rec

## What Phase II established

- **Corrected exactness:** I_comp ⇔ SmnTrackingForRep (unconditionally)
- **Regime bifurcation:** SmnTracking ⇒ Full ⇒ Weak, with Weak ↛ Full
- **Gap location:** I_rec ⇒ I_comp reduces to I_rec ⇒ SmnTrackingRecursion (under I_diag)
- Recursion taxonomy (5 notions), separation lattice
- stdAPS has I_rec ∧ I_comp ∧ I_diag
- Phase III exploration: Lawvere translation, section surjectivity hierarchy, collapse theorem, pairing shift, cardinality argument, finite countermodel (vacuous I_rec)

## What Phase III (this repo) does

Phase III **resolved** the open question: I_rec does NOT imply I_comp in abstract IndexedAPS. The smn-generated operation system need not have a local-to-global interpolation principle strong enough to turn full recursion into uniform tracking — an infinite countermodel (`sepAPS`) exhibits recursion without composition.

**Primary lens:** Clone theory / universal algebra (sections, projections, local agreement, global term realization)

**Secondary lens:** Iteration theory / parameter identity

**Negative lens:** Model-theoretic infinite countermodel construction

### Phase III established (0 sorry, 0 axioms)

- **Clone dictionary:** I_comp ↔ clone surjectivity; section surj ↔ projection surj; finite tracking ↔ local interpolation
- **Interpolation exactness:** I_comp ↔ HasFiniteTracking ∧ HasGluing
- **Parameter identity:** I_comp ↔ ParameterIdentity; I_rec ↔ PreiterationAxiom
- **Compactness schema:** Finite consistency, countermodel notions, obstruction formalized
- **Synthesis:** recursion_uniformization_theorem, section_surjectivity_characterisation
- **Separation theorem:** ∃ aps, I_rec(aps) ∧ ¬I_comp(aps). Countermodel: `sepAPS` in `Separation.lean`. See [FINAL_STATUS_AND_HANDOFF.md](FINAL_STATUS_AND_HANDOFF.md).

## File locations

| Repo | Path (local) | Key artifacts |
|------|--------------|---------------|
| Phase I | `../aps-undecidability-interfaces-lean` | APSMinimalInterface, paper |
| Phase II | `../aps-recursion-composition-uniformity-lean` | APSRecComp, PHASE_III_STATUS_AND_HANDOFF.md |
| Phase III | `.` (this repo) | APSUniformization, FINAL_STATUS_AND_HANDOFF.md, NAVIGATION.md, project_history/ |

## Handoff document

**Canonical Phase III status:** [FINAL_STATUS_AND_HANDOFF.md](FINAL_STATUS_AND_HANDOFF.md) — separation proved, story arc, theorem inventory, resolution.

Phase II handoff copy and historical specs (SPEC_V2–V5) are in `project_history/`.
