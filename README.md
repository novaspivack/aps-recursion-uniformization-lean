# APS Recursion Uniformization

**Phase III** of the APS interface program — the **final module** where the recursion–composition frontier is resolved. Clone theory / universal algebra / iteration theory attack on the recursion–composition frontier in abstract IndexedAPS.

## Role in the Program

This repository proves the **negative result**: indexed recursion does *not* imply indexed composition in abstract IndexedAPS. It also establishes the exact algebraic decomposition of composition (I_comp ⇔ FiniteTracking ∧ HasGluing). The countermodel `sepAPS` exhibits *section poverty under diagonal abundance*: it has diagonal identity, fixed points for every indexed representable total unary map, and yet fails composition because its section family is too poor to realize a tracker for a distinguished nonconstant function. Pointwise fixed-point existence is strictly weaker than uniform parameterized tracking in abstract indexed systems.

## The Three Phases

| Phase | Repository | Role |
|-------|------------|------|
| **Phase I** | [`aps-undecidability-interfaces-lean`](https://github.com/novaspivack/aps-undecidability-interfaces-lean) | Total-tier exactness, indexed interface taxonomy, separation lattice, Rice bifurcation |
| **Phase II** | [`aps-recursion-composition-uniformity-lean`](https://github.com/novaspivack/aps-recursion-composition-uniformity-lean) | Corrected exactness (I_comp ⇔ SmnTrackingForRep), recursion taxonomy, regime bifurcation |
| **Phase III** | `aps-recursion-uniformization-lean` (this repo) | **Final module:** exact algebraic decomposition (I_comp ⇔ FiniteTracking ∧ Gluing), separation theorem ∃ aps (I_rec(aps) ∧ ¬I_comp(aps)), countermodel sepAPS |

## Main result

**Separation theorem:** I_rec does NOT imply I_comp in abstract IndexedAPS.

∃ aps : IndexedAPS, I_rec(aps) ∧ ¬I_comp(aps)

Proved in Lean with **0 axioms, 0 sorry.** Countermodel: `sepAPS` in `Separation.lean`. See [FINAL_STATUS_AND_HANDOFF.md](FINAL_STATUS_AND_HANDOFF.md) §9a for the clean theorem narrative.

**Algebraic decomposition:** I_comp ⟺ FiniteTracking ∧ HasGluing (main Phase III theorem).

## Dependencies

- **Phase I:** `aps-undecidability-interfaces-lean` (APSMinimalInterface)
- **Phase II:** `aps-recursion-composition-uniformity-lean` (APSRecComp)

## Build

```bash
lake update
lake exe cache get
lake build
```

## Documentation

- **FINAL_STATUS_AND_HANDOFF.md** — Canonical handoff: full narrative, story arc, clean countermodel (§9a), resolution status
- **REPO_MAP.md** — Dependency chain, what each phase established
- **project_history/** — Historical specs (SPEC_V2–V5) and Phase II handoff copy

## Paper

The final paper lives in this repo: `paper/Composition_FT_Gluing_Separation.pdf`. See `paper/notes/PAPER_LOCATION.md`.
