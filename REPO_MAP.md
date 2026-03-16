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

## What Phase III (this repo) will do

Determine whether the smn-generated operation system of an IndexedAPS has a local-to-global interpolation principle strong enough to turn full recursion into uniform tracking — or else exhibit an infinite countermodel where recursion holds without such interpolation.

**Primary lens:** Clone theory / universal algebra (sections, projections, local agreement, global term realization)

**Secondary lens:** Iteration theory / parameter identity

**Negative lens:** Model-theoretic infinite countermodel construction

## File locations

| Repo | Path (local) | Key artifacts |
|------|--------------|---------------|
| Phase I | `../aps-undecidability-interfaces-lean` | APSMinimalInterface, paper |
| Phase II | `../aps-recursion-composition-uniformity-lean` | APSRecComp, PHASE_III_STATUS_AND_HANDOFF.md |
| Phase III | `.` (this repo) | APSUniformization, SPEC_V2.md |

## Handoff document

The comprehensive Phase II + Phase III status and handoff is in the Phase II repo:

```
../aps-recursion-composition-uniformity-lean/PHASE_III_STATUS_AND_HANDOFF.md
```

A copy is preserved in this repo as `HANDOFF_FROM_PHASE_II.md` for reference.
