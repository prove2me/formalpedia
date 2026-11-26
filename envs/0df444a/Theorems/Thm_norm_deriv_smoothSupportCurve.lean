-- Prove2me | Theorems.Thm_norm_deriv_smoothSupportCurve
-- name    : norm_deriv_smoothSupportCurve
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:26:16.638421+00:00
-- url     : https://prove2.me/theorems/3c11f035-f704-401f-b9bd-27714988e852
-- title:
--   norm deriv smooth Support Curve: norm deriv smooth Support Curve
-- statement:
--   The speed of a positive-curvature support curve is its curvature radius.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L153-L163
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L153-L163

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem norm_deriv_smoothSupportCurve {h : ℝ → ℝ}
    (hsmooth : ContDiff ℝ ∞ h)
    (hcurv : ∀ theta, 0 < smoothSupportCurvatureRadius h theta)
    (theta : ℝ) :
    ‖deriv (smoothSupportCurve h) theta‖ =
      smoothSupportCurvatureRadius h theta := by sorry
