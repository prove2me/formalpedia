-- Prove2me | Theorems.Thm_iIndepFun_block_extract
-- name    : iIndepFun_block_extract
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:35:21.745053+00:00
-- url     : https://prove2.me/theorems/cda7d8ca-53a3-4a6a-9b6a-f5ecaf27080e
-- title:
--   i Indep Fun block extract: i Indep Fun block extract
-- statement:
--   Block extractions are independent under the product measure.
--       Key infrastructure for boosting (D4) and probability amplification.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Tail.lean#L50-L109
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Tail.lean#L50-L109

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

theorem iIndepFun_block_extract {X : Type*} [MeasurableSpace X]
    (k m : ℕ) (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D] :
    ProbabilityTheory.iIndepFun (β := fun _ : Fin k => Fin m → X)
      (fun (j : Fin k) (ω : Fin (k * m) → X) => blockExtract k m ω j)
      (MeasureTheory.Measure.pi (fun _ : Fin (k * m) => D)) := by sorry
