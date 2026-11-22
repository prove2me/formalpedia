-- Prove2me | Theorems.Thm_ex_not_implies_pac
-- name    : ex_not_implies_pac
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:36:58.296894+00:00
-- url     : https://prove2.me/theorems/49b71ff5-dd9f-4642-a24f-4f81427289bb
-- title:
--   ex not implies pac: ex not implies pac
-- statement:
--   EX does not imply PAC.
--       Witness: X = ℕ, C = all indicator functions of finite subsets of ℕ.
--       EX-learnable: learner outputs "true on everything seen so far" — converges on any text.
--       Not PAC-learnable: VCDim = ⊤ (every finite set is shattered).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Separation.lean#L1122-L1193
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Separation.lean#L1122-L1193

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

theorem ex_not_implies_pac :
    ∃ (X : Type) (_ : Countable X) (_ : MeasurableSpace X) (C : ConceptClass X Bool),
      EXLearnable X C ∧ ¬ PACLearnable X C := by sorry
