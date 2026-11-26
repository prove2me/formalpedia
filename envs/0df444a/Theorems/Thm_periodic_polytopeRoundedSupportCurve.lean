-- Prove2me | Theorems.Thm_periodic_polytopeRoundedSupportCurve
-- name    : periodic_polytopeRoundedSupportCurve
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:07:51.743843+00:00
-- url     : https://prove2.me/theorems/e52175e5-ad0e-473e-a86f-c29d884d9e69
-- title:
--   periodic polytope Rounded Support Curve: periodic polytope Rounded Support Curve
-- statement:
--   The rounded polytope support curve is `2*pi`-periodic.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L206-L211
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L206-L211

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem periodic_polytopeRoundedSupportCurve
    (u : Finset ℂ) (delta rho : ℝ) :
    Function.Periodic (polytopeRoundedSupportCurve u delta rho)
      (2 * Real.pi) := by sorry
