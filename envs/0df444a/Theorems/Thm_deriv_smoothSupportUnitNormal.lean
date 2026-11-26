-- Prove2me | Theorems.Thm_deriv_smoothSupportUnitNormal
-- name    : deriv_smoothSupportUnitNormal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:04:24.081035+00:00
-- url     : https://prove2.me/theorems/c6bfc3e4-00c6-5989-bc5c-a383cc766841
-- title:
--   deriv smooth Support Unit Normal: deriv smooth Support Unit Normal
-- statement:
--   Exact derivative of the unit normal.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L92-L96
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L92-L96

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem deriv_smoothSupportUnitNormal (theta : ℝ) :
    deriv smoothSupportUnitNormal theta =
      smoothSupportUnitTangent theta := by sorry
