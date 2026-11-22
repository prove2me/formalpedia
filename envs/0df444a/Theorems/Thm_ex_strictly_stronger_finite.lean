-- Prove2me | Theorems.Thm_ex_strictly_stronger_finite
-- name    : ex_strictly_stronger_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:40:42.266961+00:00
-- url     : https://prove2.me/theorems/4faddff5-4a5f-4436-93a1-e171692f3c69
-- title:
--   ex strictly stronger finite: ex strictly stronger finite
-- statement:
--   EX learning is strictly stronger than finite learning.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Separation.lean#L1207-L1213
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Separation.lean#L1207-L1213

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Extended
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_Online
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.ProductMeasure
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_Separation
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
attribute [local instance] Classical.propDecidable
universe u v

theorem ex_strictly_stronger_finite :
    ∀ (X : Type u) (C : ConceptClass X Bool),
      FiniteLearnable X C → EXLearnable X C := by sorry
