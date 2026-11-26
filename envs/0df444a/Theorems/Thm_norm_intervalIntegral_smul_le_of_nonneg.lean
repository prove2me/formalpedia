-- Prove2me | Theorems.Thm_norm_intervalIntegral_smul_le_of_nonneg
-- name    : norm_intervalIntegral_smul_le_of_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:43:59.587017+00:00
-- url     : https://prove2.me/theorems/e2e60215-7867-478f-af22-a6b0230723c7
-- title:
--   norm interval Integral smul le of nonneg: norm interval Integral smul le of nonneg
-- statement:
--   The contractivity bound with pointwise hypotheses on `Ioc a b`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PositiveKernelBound.lean#L180-L189
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PositiveKernelBound.lean#L180-L189

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

theorem norm_intervalIntegral_smul_le_of_nonneg {K : ℝ → E →L[ℂ] E} {f : ℝ → ℂ} {a b c M : ℝ}
    (hab : a ≤ b) (hK : IntervalIntegrable K volume a b)
    (hfK : IntervalIntegrable (fun t => f t • K t) volume a b)
    (hpos : ∀ t ∈ Set.Ioc a b, 0 ≤ K t)
    (hnorm : ∫ t in a..b, K t = c • (1 : E →L[ℂ] E))
    (hc : 0 ≤ c) (hM : 0 ≤ M) (hf : ∀ t ∈ Set.Ioc a b, ‖f t‖ ≤ M) :
    ‖∫ t in a..b, f t • K t‖ ≤ c * M := by sorry
