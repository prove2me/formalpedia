-- Prove2me | Theorems.Thm_exists_tight_regular_polytopeRoundedSupportCurve
-- name    : exists_tight_regular_polytopeRoundedSupportCurve
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:31:23.572166+00:00
-- url     : https://prove2.me/theorems/fc6cc29c-0b7a-5cc5-8ca4-952b6daf9d99
-- title:
--   exists tight regular polytope Rounded Support Curve: exists tight regular polytope Rounded Support Curve
-- statement:
--   The tight-envelope parameters simultaneously give a smooth, periodic,
--   everywhere regular support curve.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelopeTight.lean#L73-L93
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelopeTight.lean#L73-L93

import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeTight
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff

theorem exists_tight_regular_polytopeRoundedSupportCurve
    {u : Finset ℂ} (hu : u.Nonempty) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta rho : ℝ,
      0 < delta ∧ 0 < rho ∧
      convexHull ℝ (u : Set ℂ) ⊆
        smoothSupportOpenEnvelope
          (polytopeRoundedSupport u delta rho) ∧
      closure
          (smoothSupportOpenEnvelope
            (polytopeRoundedSupport u delta rho)) ⊆
        Metric.thickening epsilon (convexHull ℝ (u : Set ℂ)) ∧
      Function.Periodic (polytopeRoundedSupportCurve u delta rho)
        (2 * Real.pi) ∧
      ContDiff ℝ ∞ (polytopeRoundedSupportCurve u delta rho) ∧
      ∀ theta, deriv (polytopeRoundedSupportCurve u delta rho) theta ≠ 0 := by sorry
