-- Prove2me | Theorems.Thm_norm_inner_le_of_forall_pos_le
-- name    : norm_inner_le_of_forall_pos_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:43:49.88337+00:00
-- url     : https://prove2.me/theorems/3f1bb242-7838-59bd-a3de-0caddd301155
-- title:
--   norm inner le of forall pos le: norm inner le of forall pos le
-- statement:
--   If `‖⟪x, T y⟫‖ ≤ M * ((s * (c ‖x‖²) + c ‖y‖² / s) / 2)` for every `s > 0`, then
--   `‖⟪x, T y⟫‖ ≤ c * M * ‖x‖ * ‖y‖`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PositiveKernelBound.lean#L102-L117
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PositiveKernelBound.lean#L102-L117

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

theorem norm_inner_le_of_forall_pos_le {T : E →L[ℂ] E} {c M : ℝ} (x y : E)
    (h : ∀ s : ℝ, 0 < s →
      ‖⟪x, T y⟫_ℂ‖ ≤ M * ((s * (c * ‖x‖ ^ 2) + c * ‖y‖ ^ 2 / s) / 2)) :
    ‖⟪x, T y⟫_ℂ‖ ≤ c * M * ‖x‖ * ‖y‖ := by sorry
