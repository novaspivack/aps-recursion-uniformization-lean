# Start Here — Phase III

**The recursion–composition question is resolved.**

## Resolution status (2025-03-16)

**SEPARATION PROVED.** I_rec does NOT imply I_comp in abstract IndexedAPS. `Separation.lean` + `GValRealization.lean`: **0 axioms, 0 sorry.** The countermodel `sepAPS` uses a self-sectioning non-constant function (g_val) whose section poverty prevents uniform tracking. See [FINAL_STATUS_AND_HANDOFF.md](FINAL_STATUS_AND_HANDOFF.md) §9a for the clean theorem narrative.

## Story arc

1. **Phase I** (`aps-undecidability-interfaces-lean`): Sufficiency I_comp + I_diag ⇒ I_rec
2. **Phase II** (`aps-recursion-composition-uniformity-lean`): Corrected exactness I_comp ⇔ SmnTrackingForRep, regime bifurcation, gap location
3. **Phase III** (this repo): Algebraic decomposition I_comp ⟺ FiniteTracking ∧ HasGluing; **separation proved** via countermodel sepAPS

## What to do

1. Read **[FINAL_STATUS_AND_HANDOFF.md](FINAL_STATUS_AND_HANDOFF.md)** — full narrative, §9a clean countermodel, story arc
2. Read **REPO_MAP.md** — dependency chain, what each phase established
3. Read **project_history/** — historical specs (SPEC_V2–V5) for workstreams and theorem targets
4. Build: `lake update && lake exe cache get && lake build`
