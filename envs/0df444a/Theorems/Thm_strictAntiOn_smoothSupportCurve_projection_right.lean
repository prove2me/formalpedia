-- Prove2me | Theorems.Thm_strictAntiOn_smoothSupportCurve_projection_right
-- name    : strictAntiOn_smoothSupportCurve_projection_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:07:48.67364+00:00
-- url     : https://prove2.me/theorems/f488d928-062b-4681-bcfc-049d5afde9ff
-- title:
--   strict Anti On smooth Support Curve projection right: strict Anti On smooth Support Curve projection right
-- statement:
--   After its normal angle, a positive-curvature support curve has strictly
--   decreasing projection onto that normal.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean#L116-L131
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean#L116-L131

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff

theorem strictAntiOn_smoothSupportCurve_projection_right
    {h : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ h)
    (hcurv : ∀ x, 0 < smoothSupportCurvatureRadius h x)
    (theta : ℝ) :
    StrictAntiOn
      (fun x => polytopeDirectionalValue (smoothSupportCurve h x) theta)
      (Icc theta (theta + Real.pi)) := by sorry
