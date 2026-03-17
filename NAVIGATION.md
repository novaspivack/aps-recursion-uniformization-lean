# Navigation Guide — Phase III

## Where to Start

1. **FINAL_STATUS_AND_HANDOFF.md** — Canonical handoff: separation proved, story arc, countermodel narrative (§9a), theorem inventory
2. **START_HERE.md** — Phase III resolution summary
3. **REPO_MAP.md** — Dependency chain, what each phase established
4. **project_history/** — Historical specs (SPEC_V2–V5) and Phase II handoff copy

## Module Map

```
APSUniformization.lean          # Root — imports all modules
├── Imports.lean                # Phase II (APSRecComp)
├── CloneDictionary.lean        # Tier 1 — algebraic dictionary
├── Interpolation.lean          # Tier 2 — gluing, Baker–Pixley
├── Iteration.lean              # Tier 3 — parameter identity
├── Compactness.lean            # Tier 4 — countermodel schema
├── Synthesis.lean             # Workstream E — synthesis
├── OpenQuestionAttack.lean     # Attack attempts on open question
└── IterationTransfer.lean      # Preiteration → IndexedAPS
```

## Finding Theorems

| Goal | Location |
|------|----------|
| I_comp as clone surjectivity | `CloneDictionary.I_comp_as_clone_surjectivity` |
| I_comp ↔ FiniteTracking ∧ Gluing | `Interpolation.comp_iff_finite_tracking_and_gluing` |
| I_comp ↔ ParameterIdentity | `Iteration.I_comp_as_parameter_identity` |
| Section surj ↔ Projection surj | `CloneDictionary.section_surj_as_projection_surj` |
| Finite tracking + gluing ⇒ I_comp | `Interpolation.finite_tracking_plus_X_implies_global` |
| Joint + gluing ⇒ I_comp | `Interpolation.joint_section_surj_plus_X_implies_comp` |
| Phase III synthesis | `Synthesis.phase_iii_synthesis` |

## Key Phase II Imports

Phase III depends on:
- `APSRecComp.SmnTracking` — comp_iff_smn_tracks, SmnTracks
- `APSRecComp.SmnSectionSurjectivity` — hierarchy, section_surj_at_implies_singleton_tracking
- `APSRecComp.FiniteTracking` — HasFiniteTracking, finite_tracking_and_gluing_implies_comp
- `APSRecComp.ConditionalNecessity` — corrected_exactness_iff, I_comp_and_diag_implies_rec
- `APSRecComp.SectionSurjectivityTheorems` — JointSmnSectionSurjective, joint_section_surj_and_gluing_implies_comp

## Handoff

- **Canonical status:** `FINAL_STATUS_AND_HANDOFF.md` — separation proved, story arc, outcomes, theorem inventory
- **Phase II handoff:** `project_history/HANDOFF_FROM_PHASE_II.md` (historical copy)
- **Phase II canonical:** `../aps-recursion-composition-uniformity-lean/PHASE_III_STATUS_AND_HANDOFF.md`
- **Historical specs:** `project_history/SPEC_V2.md` through `project_history/SPEC_V5.md`
