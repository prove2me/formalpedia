-- Prove2me | Theorems.Thm_norm_inner_apply_le_sqrt_mul_sqrt_of_nonneg
-- name    : norm_inner_apply_le_sqrt_mul_sqrt_of_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:43:45.518542+00:00
-- url     : https://prove2.me/theorems/5a19baf6-9494-4412-8955-793e55c970c8
-- title:
--   norm inner apply le sqrt mul sqrt of nonneg: norm inner apply le sqrt mul sqrt of nonneg
-- statement:
--   Cauchy–Schwarz for a positive operator:
--   `‖⟪x, K y⟫‖ ≤ √(re ⟪x, K x⟫) * √(re ⟪y, K y⟫)`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PositiveKernelBound.lean#L61-L68
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PositiveKernelBound.lean#L61-L68

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_Operator_Crouzeix_PositiveKernelBound
set_option autoImplicit false
open ContinuousLinearMap MeasureTheory
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem norm_inner_apply_le_sqrt_mul_sqrt_of_nonneg {K : E →L[ℂ] E} (hK : 0 ≤ K) (x y : E) :
    ‖⟪x, K y⟫_ℂ‖ ≤
      Real.sqrt (RCLike.re ⟪x, K x⟫_ℂ) * Real.sqrt (RCLike.re ⟪y, K y⟫_ℂ) := by sorry
