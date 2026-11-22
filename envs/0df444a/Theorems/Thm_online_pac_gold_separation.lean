-- Prove2me | Theorems.Thm_online_pac_gold_separation
-- name    : online_pac_gold_separation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:40:49.046005+00:00
-- url     : https://prove2.me/theorems/8a1e56d3-d881-4872-8eec-cb07bd2d6038
-- title:
--   online pac gold separation: online pac gold separation
-- statement:
--   Online-PAC-Gold three-way separation.
--       Pl-REPAIR: first conjunct had [Fintype X] which made it false.
--       Fixed to match pac_not_implies_online repair.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Separation.lean#L1218-L1223
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Separation.lean#L1218-L1223

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

theorem online_pac_gold_separation :
    (∃ (X : Type) (_ : MeasurableSpace X) (C : ConceptClass X Bool),
      PACLearnable X C ∧ ¬ OnlineLearnable X Bool C) ∧
    (∃ (X : Type) (_ : Countable X) (_ : MeasurableSpace X) (C : ConceptClass X Bool),
      EXLearnable X C ∧ ¬ PACLearnable X C) := by sorry
