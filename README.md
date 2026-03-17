# APS Recursion Uniformization

Phase III of the APS interface program. Clone theory / universal algebra / iteration theory attack on the recursion–composition frontier in abstract IndexedAPS.

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
