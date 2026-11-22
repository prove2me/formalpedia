-- Prove2me | Theorems.Thm_measurableBatchLearner_boost
-- name    : measurableBatchLearner_boost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:41:41.605179+00:00
-- url     : https://prove2.me/theorems/f2b2d37b-012c-4297-a3b6-024d46f03149
-- title:
--   measurable Batch Learner boost: measurable Batch Learner boost
-- statement:
--   Boosting preserves measurability. Majority vote is a measurable Boolean function of
--   finitely many inputs, so `boostLearner` inherits measurability via
--   `measurableBatchLearner_combine`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/Closure.lean#L81-L88
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/Closure.lean#L81-L88

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Closure
set_option autoImplicit true
@[expose] public section
public section
universe u
attribute [local instance] Classical.propDecidable

theorem measurableBatchLearner_boost
    {X : Type u} [MeasurableSpace X]
    (k : ℕ) (L : Fin k → BatchLearner X Bool)
    (hL : ∀ i, MeasurableBatchLearner X (L i)) :
    MeasurableBatchLearner X (boostLearner k L) := by sorry
