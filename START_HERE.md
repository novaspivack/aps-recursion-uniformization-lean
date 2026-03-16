# Start Here — Phase III Continuation

**Continue the recursion–composition attack in this repo.**

## Where we are

- **Phase I** (`aps-undecidability-interfaces-lean`): Sufficiency I_comp + I_diag ⇒ I_rec
- **Phase II** (`aps-recursion-composition-uniformity-lean`): Corrected exactness I_comp ⇔ SmnTrackingForRep, regime bifurcation, gap location, Phase III exploration (Lawvere, section surjectivity, collapse theorem, pairing shift)
- **Phase III** (this repo): Clone theory / universal algebra / iteration theory attack

## What to do

1. Read **REPO_MAP.md** — dependency chain, what each phase established
2. Read **SPEC_V2.md** — workstreams A–E, theorem targets, acceptance criteria
3. Read **HANDOFF_FROM_PHASE_II.md** — reference to full Phase II handoff
4. Build: `lake update && lake exe cache get && lake build`
5. Attack **Tier 1** first: clone_dictionary_for_smn, finite_tracking_as_local_interpolation, section_surj_as_projection_surj

## Key constraint

Treat the open problem as a **uniformization problem**, not merely a self-reference problem. Prefer theorem targets that translate APS notions into algebraic/categorical ones.
