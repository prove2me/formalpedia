-- Prove2me | Theorems.Thm_vcdim_infinite_not_pac
-- name    : vcdim_infinite_not_pac
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:34:11.576932+00:00
-- url     : https://prove2.me/theorems/6050cba6-9199-4004-a258-76616cc4de61
-- title:
--   vcdim infinite not pac: vcdim infinite not pac
-- statement:
--   If VCDim = ⊤, then C is not PAC learnable.
--       Proof: for any learner L with sample function mf, pick ε = 1 / 4, δ = 1 / 4.
--       Let m = mf(1 / 4, 1 / 4). Since VCDim = ⊤, ∃ shattered set S with |S| ≥ 2m.
--       Put D = uniform on S. For random labeling, any m-sample learner
--       has expected error ≥ 1 / 4 on unseen points.
--       This is the core of pac_imp_vcdim_finite (contrapositive direction).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Tail.lean#L195-L240
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Tail.lean#L195-L240

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_VCDimension
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Mathlib.Probability.Independence.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Probability.ProductMeasure
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem vcdim_infinite_not_pac (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) (hinf : VCDim X C = ⊤) :
    ¬ PACLearnable X C := by sorry
