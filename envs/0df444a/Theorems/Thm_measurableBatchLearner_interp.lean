-- Prove2me | Theorems.Thm_measurableBatchLearner_interp
-- name    : measurableBatchLearner_interp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:41:48.907482+00:00
-- url     : https://prove2.me/theorems/77db6028-a862-48c9-80fd-e6e6c1c38d8b
-- title:
--   measurable Batch Learner interp: measurable Batch Learner interp
-- statement:
--   `interpLearner` preserves measurability when the region `A` is measurable. The
--   indicator of `A` composed with `Measurable.ite` and the two component learners gives a
--   measurable conditional selector.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/Closure.lean#L107-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/Closure.lean#L107-L118

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Closure
set_option autoImplicit true
@[expose] public section
public section
universe u
attribute [local instance] Classical.propDecidable

theorem measurableBatchLearner_interp
    {X : Type u} [MeasurableSpace X]
    (A : Set X) (hA : MeasurableSet A)
    (L₁ L₂ : BatchLearner X Bool)
    (h₁ : MeasurableBatchLearner X L₁)
    (h₂ : MeasurableBatchLearner X L₂) :
    MeasurableBatchLearner X (interpLearner A L₁ L₂) := by sorry
