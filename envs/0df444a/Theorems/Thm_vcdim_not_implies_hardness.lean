-- Prove2me | Theorems.Thm_vcdim_not_implies_hardness
-- name    : vcdim_not_implies_hardness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:42:25.572642+00:00
-- url     : https://prove2.me/theorems/700b230a-f000-4f1b-8034-5861fe527390
-- title:
--   vcdim not implies hardness: vcdim not implies hardness
-- statement:
--   VC dimension does not determine SQ hardness:
--       there exists a concept class with finite VC dimension but infinite SQ dimension
--       under some distribution at some positive correlation threshold.
--       Witness: singleton indicators on ℕ, with SQDimension = ⊤ at τ = 1.
--       For any probability D on ℕ, the correlation between distinct indicators 1_i, 1_j
--       is |1 - 2(D({i}) + D({j}))| ≤ 1, so every finite subset of C qualifies at τ = 1.
--       Since C is infinite, SQDimension = ⊤.
--       The statement quantifies the measurable domain, distribution, and threshold
--       parameters used by `SQDimension`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Extended.lean#L1058-L1148
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/Extended.lean#L1058-L1148

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_Extended
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem vcdim_not_implies_hardness :
    ∃ (X : Type) (_ : MeasurableSpace X) (C : ConceptClass X Bool),
      VCDim X C < ⊤ ∧
      ∃ (D : MeasureTheory.Measure X) (_ : MeasureTheory.IsProbabilityMeasure D)
        (τ : ℝ), 0 < τ ∧ SQDimension X C D τ = ⊤ := by sorry
