-- Prove2me | Theorems.Thm_contDiff_smoothSupportCurve
-- name    : contDiff_smoothSupportCurve
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:08:32.885741+00:00
-- url     : https://prove2.me/theorems/7dc56a2c-a13b-48b5-bbf2-9a3ae7e343be
-- title:
--   cont Diff smooth Support Curve: cont Diff smooth Support Curve
-- statement:
--   A smooth support function produces an infinitely differentiable support
--   curve.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L83-L89
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L83-L89

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem contDiff_smoothSupportCurve {h : ℝ → ℝ}
    (hsmooth : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (smoothSupportCurve h) := by sorry
