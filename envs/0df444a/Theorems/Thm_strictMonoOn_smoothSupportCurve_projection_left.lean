-- Prove2me | Theorems.Thm_strictMonoOn_smoothSupportCurve_projection_left
-- name    : strictMonoOn_smoothSupportCurve_projection_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:07:51.021473+00:00
-- url     : https://prove2.me/theorems/b9e8e63c-0da4-4884-9bc0-f91480dcc79d
-- title:
--   strict Mono On smooth Support Curve projection left: strict Mono On smooth Support Curve projection left
-- statement:
--   Before its normal angle, a positive-curvature support curve has strictly
--   increasing projection onto that normal.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean#L97-L112
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean#L97-L112

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff

theorem strictMonoOn_smoothSupportCurve_projection_left
    {h : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ h)
    (hcurv : ∀ x, 0 < smoothSupportCurvatureRadius h x)
    (theta : ℝ) :
    StrictMonoOn
      (fun x => polytopeDirectionalValue (smoothSupportCurve h x) theta)
      (Icc (theta - Real.pi) theta) := by sorry
