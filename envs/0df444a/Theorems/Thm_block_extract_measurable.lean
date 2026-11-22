-- Prove2me | Theorems.Thm_block_extract_measurable
-- name    : block_extract_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:35:21.719703+00:00
-- url     : https://prove2.me/theorems/67e68804-022f-4681-ae9d-549a1e7db480
-- title:
--   block extract measurable: block extract measurable
-- statement:
--   Block extraction is measurable: extracting block j from a pi-type is measurable.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Tail.lean#L43-L46
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Tail.lean#L43-L46

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

theorem block_extract_measurable {X : Type*} [MeasurableSpace X]
    (k m : ℕ) (j : Fin k) :
    Measurable (fun (ω : Fin (k * m) → X) => blockExtract k m ω j) := by sorry
