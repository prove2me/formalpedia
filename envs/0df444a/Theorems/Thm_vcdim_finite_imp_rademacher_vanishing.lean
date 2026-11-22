-- Prove2me | Theorems.Thm_vcdim_finite_imp_rademacher_vanishing
-- name    : vcdim_finite_imp_rademacher_vanishing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:35:21.381337+00:00
-- url     : https://prove2.me/theorems/005f1269-1dc7-4399-93bc-3d918251a4df
-- title:
--   vcdim finite imp rademacher vanishing: vcdim finite imp rademacher vanishing
-- statement:
--   VCDim finite → Rademacher vanishes uniformly.
--       The bound m₀ depends only on d and ε, NOT on D.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Rademacher.lean#L1671-L1751
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Rademacher.lean#L1671-L1751

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem vcdim_finite_imp_rademacher_vanishing (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (hvcdim : VCDim X C < ⊤) :
    ∀ ε > 0, ∃ m₀, ∀ (D : MeasureTheory.Measure X),
      MeasureTheory.IsProbabilityMeasure D →
      ∀ m ≥ m₀, RademacherComplexity X C D m < ε := by sorry
