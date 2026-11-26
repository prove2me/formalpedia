-- Prove2me | Theorems.Thm_intervalIntegral_resolvent_doubleLayer_eq_four_pi_smul_one_of_cauchy
-- name    : intervalIntegral_resolvent_doubleLayer_eq_four_pi_smul_one_of_cauchy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:44:57.928893+00:00
-- url     : https://prove2.me/theorems/0cf5dae9-1206-55a3-9d99-3ed04b4666df
-- title:
--   interval Integral resolvent double Layer eq four pi smul one of cauchy: interval Integral resolvent double Layer eq four pi smul one of cauchy
-- statement:
--   If the parametrized resolvent has its expected Cauchy integral
--   `2 * pi * i • 1`, then the associated outward-normal double-layer kernel
--   has total mass `4 * pi • 1`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/DoubleLayerIntegral.lean#L65-L109
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/DoubleLayerIntegral.lean#L65-L109

import Definitions.Def_Operator_Crouzeix_AdjointIntegral
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem intervalIntegral_resolvent_doubleLayer_eq_four_pi_smul_one_of_cauchy
    (A : E →L[ℂ] E) (gamma : ℝ → ℂ)
    (hint : IntervalIntegrable
      (fun t ↦ deriv gamma t • resolvent A (gamma t)) volume 0 (2 * Real.pi))
    (hCauchy : (∫ t in (0 : ℝ)..(2 * Real.pi),
      deriv gamma t • resolvent A (gamma t)) =
        (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E)) :
    (∫ t in (0 : ℝ)..(2 * Real.pi),
      ((-I * deriv gamma t) • resolvent A (gamma t)) +
        ContinuousLinearMap.adjoint
          ((-I * deriv gamma t) • resolvent A (gamma t))) =
      (4 * Real.pi) • (1 : E →L[ℂ] E) := by sorry
