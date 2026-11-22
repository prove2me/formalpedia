-- Prove2me | Theorems.Thm_measurableBatchLearner_concat
-- name    : measurableBatchLearner_concat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:37:19.922607+00:00
-- url     : https://prove2.me/theorems/102ecc32-26ea-4f4f-93c5-9d6341cdf3e8
-- title:
--   measurable Batch Learner concat: measurable Batch Learner concat
-- statement:
--   `concatLearner` preserves measurability when the selector is measurable and the
--   family is uniformly measurable. Composes the selector's measurability with the
--   family's uniform measurability to obtain joint measurability of the evaluation map in
--   `(S, x)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/Closure.lean#L164-L176
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/Closure.lean#L164-L176

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Closure
set_option autoImplicit true
@[expose] public section
public section
universe u
attribute [local instance] Classical.propDecidable

theorem measurableBatchLearner_concat
    {X : Type u} [MeasurableSpace X]
    (L : ℕ → BatchLearner X Bool)
    [hL : UniformMeasurableBatchFamily L]
    (sel : {m : ℕ} → (Fin m → X × Bool) → ℕ)
    (hsel : ∀ m, Measurable (fun S : Fin m → X × Bool => @sel m S)) :
    MeasurableBatchLearner X (concatLearner L sel) := by sorry
