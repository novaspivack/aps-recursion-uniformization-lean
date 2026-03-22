# aps-recursion-uniformization-lean — Full artifact manifest

**Toolchain:** leanprover/lean4 — pinned in `lean-toolchain` / `lakefile.lean`  
**Mathlib:** v4.29.0-rc6 (via lake)  
**Build:** From this directory: `lake update && lake exe cache get && lake build`  
**Root library import:** `APSUniformization.lean` (imports all production modules under `APSUniformization/` except `Countermodel.lean`; see root module note)  
**Executable:** `Main.lean` (`lake exe aps_recursion_uniformization_lean`)  
**Last verified:** 2026-03-21 — status per `FINAL_STATUS_AND_HANDOFF.md`: bare-APS program closed; separation and main Phase III theorems **0 axioms, 0 sorry** on the shipped import path (see Sorry status).

---

## Dependencies (sibling repos + Mathlib)

| Dependency | Role |
|------------|------|
| `../aps-undecidability-interfaces-lean` | Phase I — frozen APS / undecidability interface (`APSMinimalInterface`, etc.) |
| `../aps-recursion-composition-uniformity-lean` | Phase II — recursion–composition uniformity (`APSRecComp`) |
| Mathlib 4 | `https://github.com/leanprover-community/mathlib4` @ `v4.29.0-rc6` (not duplicated in NEMS `Combined_Lean_Manifests.md`; assumed) |

Phase III imports Phase I/II via `APSUniformization/Imports.lean`. The NEMS suite concatenates **separate** `MANIFEST.md` files for Phase I, Phase II, and Phase III in dependency order — not Mathlib.

---

## Sorry status

- **Shipped import tree** (`APSUniformization.lean` and everything it imports): **no `sorry`** in proof terms for the closed Phase III theorems (see `FINAL_STATUS_AND_HANDOFF.md`).
- **Orphan module:** `Countermodel.lean` is **not** imported by `APSUniformization.lean`; it retains a single `sorry` (see file header — historical `extMinimalAPS` attempt). `rg '\bsorry\b' APSUniformization/` therefore still matches `Countermodel.lean`.
- **Note:** The separation witness for **I_rec ∧ ¬I_comp** is `sepAPS` in `Separation.lean` with realization in `GValRealization.lean`, not `Countermodel.lean`.

---

## Theorem spine (Phase III — summary)

| Result | Location (indicative) |
|--------|------------------------|
| **I_comp ⟺ FiniteTracking ∧ HasGluing** | Algebraic characterization of composition (main Phase III theorem); see `GapClosure.lean`, `Synthesis.lean`, and related modules per `APSUniformization.lean` tier comments |
| **Separation:** ∃ indexed APS with **I_rec ∧ ¬I_comp** | `Separation.lean`, realization `GValRealization.lean` |
| **T6 route false** | `T6Counterexample.lean` (Baire/topological shortcut ruled out) |
| Failure-set geometry, section classes, gluing hierarchy | `FailureSetGeometry.lean`, `SectionClassGeometry.lean`, `GluingHierarchy.lean`, etc. |

Full narrative and sealing verdict: **`FINAL_STATUS_AND_HANDOFF.md`**, **`README.md`**, **`paper/`** (LaTeX).

---

## Layout

| Area | Path |
|------|------|
| Phase III modules | `APSUniformization/` |
| Root re-exports | `APSUniformization.lean` |
| CLI stub | `Main.lean` |
| Lake / toolchain | `lakefile.lean`, `lean-toolchain` |

---

## Module inventory (`APSUniformization/`)

| File | Role |
|------|------|
| `Imports.lean` | Imports Phase I + II libraries (`APSRecComp`, etc.) |
| `CloneDictionary.lean` | Clone / SMN dictionary; composition as surjectivity-flavored statements |
| `Interpolation.lean` | Finite tracking, gluing, Baker–Pixley–style bridges |
| `Iteration.lean` | Pre-iteration vs composition, parameter identity |
| `Compactness.lean` | Compactness / consistency schema layer for countermodel discussion |
| `Synthesis.lean` | Synthesis of algebraic routes |
| `OpenQuestionAttack.lean` | Structured attack on the open I_rec ⇒ I_comp question |
| `IterationTransfer.lean` | Transfer lemmas along iteration |
| `OutcomeAttack.lean` | Outcome-oriented proof attempts |
| `StrongSuccessAttack.lean` | Strong-success route |
| `GapClosure.lean` | Gap structure and closure lemmas |
| `PositiveAttack.lean` | Positive (sufficient-condition) routes |
| `BaireSpaceOfDiagonals.lean` | Baire / diagonal space setup |
| `FixedPointBasins.lean` | Fixed-point basins |
| `MeagernessOfBasins.lean` | Meagerness of basins |
| `BaireCoverArgument.lean` | Baire cover line |
| `PositiveResolution.lean` | Positive resolution attempts |
| `TrackerFailureRel.lean` | Tracker vs failure-set relations |
| `SectionClassGeometry.lean` | Section classes and geometry |
| `FailureSetGeometry.lean` | Failure-set definitions and lemmas (e.g. `mem_tracker_failure_set_iff`, coherence) |
| `GluingHierarchy.lean` | Gluing hierarchy |
| `UniformizationPrinciples.lean` | Uniformization principles bundle |
| `T6Counterexample.lean` | Counterexample showing the T6 / Baire shortcut fails |
| `Separation.lean` | Separation theorem ∃ **I_rec ∧ ¬I_comp** (`sepAPS`) |
| `GValRealization.lean` | Realization lemmas for the separating witness |
| `Countermodel.lean` | Legacy / alternate countermodel material — **not** imported by `APSUniformization.lean` (see root module) |

---

## Related documentation

- **`README.md`** — clone layout, build, dependency repos  
- **`FINAL_STATUS_AND_HANDOFF.md`** — closure status, four-pillar summary, what not to reopen  
- **`paper/`** — APS uniformization LaTeX (`main.tex`, sections)  
- **`notes/`** — `LEAN_STATUS.md`, `REPO_MAP.md`, planning notes  
