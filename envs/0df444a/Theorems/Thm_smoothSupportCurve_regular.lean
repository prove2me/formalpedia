-- Prove2me | Theorems.Thm_smoothSupportCurve_regular
-- name    : smoothSupportCurve_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:09:03.120647+00:00
-- url     : https://prove2.me/theorems/8fa9febd-8fa8-40e4-9512-c711cc077aa7
-- title:
--   smooth Support Curve regular: smooth Support Curve regular
-- statement:
--   Positive curvature radius makes the support curve regular.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L138-L150
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L138-L150

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem smoothSupportCurve_regular {h : ℝ → ℝ}
    (hsmooth : ContDiff ℝ ∞ h)
    (hcurv : ∀ theta, 0 < smoothSupportCurvatureRadius h theta)
    (theta : ℝ) :
    deriv (smoothSupportCurve h) theta ≠ 0 := by sorry
