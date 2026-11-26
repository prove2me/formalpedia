-- Prove2me | Theorems.Thm_neg_I_mul_deriv_smoothSupportCurve
-- name    : neg_I_mul_deriv_smoothSupportCurve
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:26:26.044374+00:00
-- url     : https://prove2.me/theorems/18e4e2f3-74bb-4538-9258-4b751a6ee098
-- title:
--   neg I mul deriv smooth Support Curve: neg I mul deriv smooth Support Curve
-- statement:
--   Rotating the positive tangent velocity clockwise gives the outward normal
--   scaled by the curvature radius.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L167-L180
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L167-L180

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem neg_I_mul_deriv_smoothSupportCurve {h : ℝ → ℝ}
    (hsmooth : ContDiff ℝ ∞ h) (theta : ℝ) :
    -I * deriv (smoothSupportCurve h) theta =
      smoothSupportCurvatureRadius h theta •
        smoothSupportUnitNormal theta := by sorry
