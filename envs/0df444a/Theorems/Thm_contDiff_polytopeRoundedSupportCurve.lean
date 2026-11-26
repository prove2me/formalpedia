-- Prove2me | Theorems.Thm_contDiff_polytopeRoundedSupportCurve
-- name    : contDiff_polytopeRoundedSupportCurve
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:08:28.003898+00:00
-- url     : https://prove2.me/theorems/5d120d5d-6e5b-5f62-9e34-37fac57b0b90
-- title:
--   cont Diff polytope Rounded Support Curve: cont Diff polytope Rounded Support Curve
-- statement:
--   The rounded polytope support curve is infinitely differentiable.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L214-L218
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L214-L218

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem contDiff_polytopeRoundedSupportCurve
    {u : Finset ℂ} (hu : u.Nonempty) (delta rho : ℝ) :
    ContDiff ℝ ∞ (polytopeRoundedSupportCurve u delta rho) := by sorry
