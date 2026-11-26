-- Prove2me | Theorems.Thm_inner_apply_eq_inner_cfcSqrt_of_nonneg
-- name    : inner_apply_eq_inner_cfcSqrt_of_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:42:19.547483+00:00
-- url     : https://prove2.me/theorems/98873039-b53d-532b-9435-8d3ed708c2bb
-- title:
--   inner apply eq inner cfc Sqrt of nonneg: inner apply eq inner cfc Sqrt of nonneg
-- statement:
--   For a positive operator `K`, `⟪x, K y⟫ = ⟪√K x, √K y⟫`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PositiveKernelBound.lean#L47-L52
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PositiveKernelBound.lean#L47-L52

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

theorem inner_apply_eq_inner_cfcSqrt_of_nonneg {K : E →L[ℂ] E} (hK : 0 ≤ K) (x y : E) :
    ⟪x, K y⟫_ℂ = ⟪CFC.sqrt K x, CFC.sqrt K y⟫_ℂ := by sorry
