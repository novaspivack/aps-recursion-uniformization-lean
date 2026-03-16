# APS Recursion Uniformization

Phase III of the APS interface program. Clone theory / universal algebra / iteration theory attack on the recursion–composition frontier in abstract IndexedAPS.

## Dependencies

- **Phase I:** `aps-undecidability-interfaces-lean` (APSMinimalInterface)
- **Phase II:** `aps-recursion-composition-uniformity-lean` (APSRecComp)

## Build

```bash
lake update
lake exe cache get
lake build
```

## Mission

Determine whether the smn-generated operation system of an IndexedAPS has a local-to-global interpolation principle strong enough to turn full recursion into uniform tracking — or else exhibit an infinite countermodel where recursion holds without such interpolation.

## Documentation

- `REPO_MAP.md` — Dependency chain, what each phase established
- `SPEC_V2.md` — Full research spec (workstreams, theorem targets)
- `HANDOFF_FROM_PHASE_II.md` — Reference to Phase II handoff

## Paper

The unified paper (Phase I + Phase II) lives in the Phase I repo:

`../aps-undecidability-interfaces-lean/paper/01_Minimal_Interfaces/Minimal_Interfaces_for_Undecidability.pdf`
