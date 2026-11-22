-- Prove2me | Theorems.Thm_cosh_le_exp_sq_half
-- name    : cosh_le_exp_sq_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:35:17.1292+00:00
-- url     : https://prove2.me/theorems/535864d9-dbaf-4612-9f79-d97b2af26f65
-- title:
--   cosh le exp sq half: cosh le exp sq half
-- statement:
--   cosh(x) ≤ exp(x²/2). Standard sub-Gaussian bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Rademacher.lean#L327-L328
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Rademacher.lean#L327-L328

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem cosh_le_exp_sq_half (x : ℝ) : Real.cosh x ≤ Real.exp (x ^ 2 / 2) := by sorry
