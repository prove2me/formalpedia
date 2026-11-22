-- Prove2me | Theorems.Thm_vcdim_finite_imp_pac
-- name    : vcdim_finite_imp_pac
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:36:35.76446+00:00
-- url     : https://prove2.me/theorems/8e634fbf-7588-4636-9723-a5d81acd559f
-- title:
--   vcdim finite imp pac: vcdim finite imp pac
-- statement:
--   Direction ←: finite VCDim implies PAC learnability.
--
--       PROOF ROUTE (via new infrastructure in Generalization.lean):
--       Step 1: VCDim < ∞ → HasUniformConvergence (vcdim_finite_imp_uc)
--         Sub-step 1a: Sauer-Shelah gives GrowthFunction bound
--         Sub-step 1b: Symmetrization reduces UC to growth function counting
--         Sub-step 1c: Concentration inequality closes the bound
--       Step 2: HasUniformConvergence → PACLearnable (uc_imp_pac)
--         Sub-step 2a: Construct ERM learner
--         Sub-step 2b: ERM is consistent in realizable case
--         Sub-step 2c: Consistent + UC → low TrueError
--
--       The proof handles the empty concept class separately before constructing
--       an ERM learner for the nonempty case.
--
--       **Counterdefinition (COUNTER-4):** If the ERM approach fails for computational
--       reasons (ERM is noncomputable, and we need a computable learner for
--       computational learning theory), swap to the compression-based proof:
--       VCDim < ∞ → finite compression scheme (Moran-Yehudayoff 2016)
--       → compression scheme learner is PAC.
--       **Swap condition:** When proving COMPUTATIONAL PAC learnability (polynomial time).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/PAC.lean#L74-L87
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/PAC.lean#L74-L87

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Compression
public import Definitions.Def_LeanPool_FormalLearningTheory_Bridge
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GeneralizationResults
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_PAC
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem vcdim_finite_imp_pac (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (hC : VCDim X C < ⊤)
    [MeasurableConceptClass X C] :
    PACLearnable X C := by sorry
