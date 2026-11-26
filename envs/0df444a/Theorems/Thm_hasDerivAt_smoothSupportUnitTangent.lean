-- Prove2me | Theorems.Thm_hasDerivAt_smoothSupportUnitTangent
-- name    : hasDerivAt_smoothSupportUnitTangent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:24:02.839813+00:00
-- url     : https://prove2.me/theorems/90ed7d5c-a34f-5095-b5f4-5df067cee16a
-- title:
--   has Deriv At smooth Support Unit Tangent: has Deriv At smooth Support Unit Tangent
-- statement:
--   Derivative witness for the unit tangent.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L110-L115
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L110-L115

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem hasDerivAt_smoothSupportUnitTangent (theta : ℝ) :
    HasDerivAt smoothSupportUnitTangent
      (-smoothSupportUnitNormal theta) theta := by sorry
