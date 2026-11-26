-- Prove2me | Theorems.Thm_opNorm_le_of_forall_norm_inner_le
-- name    : opNorm_le_of_forall_norm_inner_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:43:49.128286+00:00
-- url     : https://prove2.me/theorems/d287c829-b83f-4c71-bee6-ffe23f7c442d
-- title:
--   op Norm le of forall norm inner le: op Norm le of forall norm inner le
-- statement:
--   An operator whose matrix coefficients are bounded by `M * ‖x‖ * ‖y‖` has norm at most `M`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PositiveKernelBound.lean#L72-L85
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PositiveKernelBound.lean#L72-L85

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
omit [CompleteSpace E]

theorem opNorm_le_of_forall_norm_inner_le {T : E →L[ℂ] E} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ x y : E, ‖⟪x, T y⟫_ℂ‖ ≤ M * ‖x‖ * ‖y‖) : ‖T‖ ≤ M := by sorry
