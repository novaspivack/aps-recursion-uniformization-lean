import APSUniformization.Imports
import APSUniformization.CloneDictionary
import APSUniformization.Interpolation
import APSUniformization.Iteration
import APSUniformization.Compactness
import APSUniformization.Synthesis
import APSUniformization.OpenQuestionAttack
import APSUniformization.IterationTransfer
import APSUniformization.OutcomeAttack
import APSUniformization.StrongSuccessAttack
import APSUniformization.GapClosure
import APSUniformization.PositiveAttack
import APSUniformization.BaireSpaceOfDiagonals
import APSUniformization.FixedPointBasins
import APSUniformization.MeagernessOfBasins
import APSUniformization.BaireCoverArgument
import APSUniformization.PositiveResolution
import APSUniformization.TrackerFailureRel
import APSUniformization.SectionClassGeometry
import APSUniformization.FailureSetGeometry
import APSUniformization.GluingHierarchy
import APSUniformization.UniformizationPrinciples
import APSUniformization.T6Counterexample
import APSUniformization.Separation
-- NOTE: Countermodel.lean is NOT imported — earlier `extMinimalAPS` attempt (not I_rec).
-- See FINAL_STATUS_AND_HANDOFF.md (countermodel status / §9). The settled negative answer
-- uses `sepAPS` in Separation.lean + GValRealization.lean, not Countermodel.lean.

/-!
# APS Recursion Uniformization — Phase III Research

Clone theory / universal algebra / iteration theory attack on the recursion–composition frontier.

Depends on:
- `aps-undecidability-interfaces-lean` (Phase I)
- `aps-recursion-composition-uniformity-lean` (Phase II)

## Tier 1 — Algebraic dictionary (Workstream A)
- `clone_dictionary_for_smn`, `I_comp_as_clone_surjectivity`, `finite_tracking_as_local_interpolation`, `section_surj_as_projection_surj`

## Tier 2 — Interpolation (Workstream B)
- `finite_tracking_plus_X_implies_global`, `joint_section_surj_plus_X_implies_comp`, `baker_pixley_candidate_X`
- `comp_iff_finite_tracking_and_gluing`: I_comp ↔ FiniteTracking ∧ Gluing

## Tier 3 — Iteration translation (Workstream C)
- `I_rec_as_preiteration_axiom`, `I_comp_as_parameter_identity`, `smn_spec_as_parameterization_schema`
- `aps_parameter_identity_bridge`, `preiteration_gap_structure`

## Tier 4 — Infinite countermodel (Workstream D)
- `finite_consistency_schema`, `compactness_countermodel_candidate`, `compactness_obstruction`

## Workstream E — Synthesis
- `recursion_uniformization_theorem`, `aps_interpolation_exactness`, `section_surjectivity_characterisation`, `recursion_comp_independence_schema`, `phase_iii_synthesis`

## SPEC_V3 — Baire-category attack (historical; T6 proved false)
- `DiagonalFiber`, `NowhereDenseInFiber`, `MeagerInFiber`, `baire_category_fiber`
- `FixedPointBasin`, `basin_characterization`, `basin_ext_constraint`
- `all_meager_not_covered` (T8, proved), `I_rec_implies_nonmeager_basin` (T9, proved)
- T6, T7, T10, T11, T12: commented out (T6 proved false; rest depended on T6)

## Option 8 — Tracker failure relation (structural lemmas preserved)
- `TrackerFailureRel`, `SectionFailureUniformizes`, `NonmeagerBasinImpliesSectionSurj`
- Proved: Target A, singleton C, extensional trackers, same-section coherence, F_k membership
- Commented out: C multi-element, D, C' special/general, E (uniformization fails in general)

## SPEC_V4 — Uniformization Geometry (explanatory aftermath)
- `SectionClassGeometry`: σ_k(x), SectionMatchesTargetAt, invariance laws
- `FailureSetGeometry`: PairwiseFailureIntersection, FiniteFailureIntersection, Helly-type
- `GluingHierarchy`: HasSingletonGluing, HasPairwiseGluing, gluing ladder
- `UniformizationPrinciples`: taxonomy (pointwise, finite, basin, amalgamation, failure-set)
- `T6Counterexample`: T6 as stated is FALSE — basin can be whole fiber when e ∈ DiagonalRange

## SPEC_V5 — Separation
- `GValRealization`: concrete g_val definition, 0 sorry
- `Separation`: sepAPS — I_rec ∧ ¬I_comp, 0 axioms, 0 sorry
-/
