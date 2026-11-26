-- Prove2me | Theorems.Thm_re_inner_apply_self_eq_norm_cfcSqrt_sq_of_nonneg
-- name    : re_inner_apply_self_eq_norm_cfcSqrt_sq_of_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:43:40.011615+00:00
-- url     : https://prove2.me/theorems/95343cc5-d5be-43e2-8007-86319c6e123f
-- title:
--   re inner apply self eq norm cfc Sqrt sq of nonneg: re inner apply self eq norm cfc Sqrt sq of nonneg
-- statement:
--   For a positive operator `K`, `re ⟪x, K x⟫ = ‖√K x‖ ^ 2`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PositiveKernelBound.lean#L55-L57
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PositiveKernelBound.lean#L55-L57

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

theorem re_inner_apply_self_eq_norm_cfcSqrt_sq_of_nonneg {K : E →L[ℂ] E} (hK : 0 ≤ K) (x : E) :
    RCLike.re ⟪x, K x⟫_ℂ = ‖CFC.sqrt K x‖ ^ 2 := by sorry
