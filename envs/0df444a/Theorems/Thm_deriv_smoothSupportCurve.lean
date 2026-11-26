-- Prove2me | Theorems.Thm_deriv_smoothSupportCurve
-- name    : deriv_smoothSupportCurve
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:04:08.944495+00:00
-- url     : https://prove2.me/theorems/6e33aeec-bd2d-5692-89f7-597298f287ba
-- title:
--   deriv smooth Support Curve: deriv smooth Support Curve
-- statement:
--   Exact velocity formula for a smooth support curve.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L118-L135
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L118-L135

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem deriv_smoothSupportCurve {h : ℝ → ℝ}
    (hsmooth : ContDiff ℝ ∞ h) (theta : ℝ) :
    deriv (smoothSupportCurve h) theta =
      smoothSupportCurvatureRadius h theta •
        smoothSupportUnitTangent theta := by sorry
