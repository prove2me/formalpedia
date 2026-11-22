-- Prove2me | Theorems.Thm_measurableBatchLearner_combine
-- name    : measurableBatchLearner_combine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:34:46.063594+00:00
-- url     : https://prove2.me/theorems/05398d5b-9663-4138-ab7a-4a64d24f4eea
-- title:
--   measurable Batch Learner combine: measurable Batch Learner combine
-- statement:
--   `combineLearner` preserves `MeasurableBatchLearner` whenever the combiner `F` is
--   jointly measurable. Factored through measurability of coordinate projections in the
--   product σ-algebra.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/Closure.lean#L51-L64
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/Closure.lean#L51-L64

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Closure
set_option autoImplicit true
@[expose] public section
public section
universe u
attribute [local instance] Classical.propDecidable

theorem measurableBatchLearner_combine
    {X : Type u} [MeasurableSpace X]
    (k : ℕ) (F : X → (Fin k → Bool) → Bool)
    (hF : Measurable (fun p : X × (Fin k → Bool) => F p.1 p.2))
    (L : Fin k → BatchLearner X Bool)
    (hL : ∀ i, MeasurableBatchLearner X (L i)) :
    MeasurableBatchLearner X (combineLearner k F L) := by sorry
