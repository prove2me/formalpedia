-- Prove2me | Theorems.Thm_deriv_smoothSupportUnitTangent
-- name    : deriv_smoothSupportUnitTangent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:05:19.387181+00:00
-- url     : https://prove2.me/theorems/f6e9940f-49fc-4851-88a0-a26bab6e47c6
-- title:
--   deriv smooth Support Unit Tangent: deriv smooth Support Unit Tangent
-- statement:
--   Exact derivative of the unit tangent.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L99-L107
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L99-L107

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem deriv_smoothSupportUnitTangent (theta : ℝ) :
    deriv smoothSupportUnitTangent theta =
      -smoothSupportUnitNormal theta := by sorry
