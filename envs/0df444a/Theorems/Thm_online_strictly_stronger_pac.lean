-- Prove2me | Theorems.Thm_online_strictly_stronger_pac
-- name    : online_strictly_stronger_pac
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:40:41.336532+00:00
-- url     : https://prove2.me/theorems/96aad2cd-90d9-42dd-8507-dabd3ba95bff
-- title:
--   online strictly stronger pac: online strictly stronger pac
-- statement:
--   Online learning is strictly stronger than PAC learning.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Separation.lean#L1196-L1204
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Separation.lean#L1196-L1204

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

theorem online_strictly_stronger_pac :
    (∀ (X : Type) [MeasurableSpace X] (C : ConceptClass X Bool)
      [MeasurableConceptClass X C],
      OnlineLearnable X Bool C → PACLearnable X C) ∧
    (∃ (X : Type) (_ : MeasurableSpace X) (C : ConceptClass X Bool),
      PACLearnable X C ∧ ¬ OnlineLearnable X Bool C) := by sorry
