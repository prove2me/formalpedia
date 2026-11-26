-- Prove2me | Theorems.Thm_periodic_smoothSupportUnitTangent
-- name    : periodic_smoothSupportUnitTangent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:06:33.951478+00:00
-- url     : https://prove2.me/theorems/c9776272-f8a2-599d-a52e-72c1a436def7
-- title:
--   periodic smooth Support Unit Tangent: periodic smooth Support Unit Tangent
-- statement:
--   The unit tangent is `2*pi`-periodic.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L56-L58
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L56-L58

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem periodic_smoothSupportUnitTangent :
    Function.Periodic smoothSupportUnitTangent (2 * Real.pi) := by sorry
