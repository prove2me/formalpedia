-- Prove2me | Theorems.Thm_contDiff_smoothSupportUnitTangent
-- name    : contDiff_smoothSupportUnitTangent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:04:09.304623+00:00
-- url     : https://prove2.me/theorems/8053b6c3-3c66-4bdd-bbf0-5b08d91e9529
-- title:
--   cont Diff smooth Support Unit Tangent: cont Diff smooth Support Unit Tangent
-- statement:
--   The unit tangent is infinitely differentiable.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L77-L79
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L77-L79

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem contDiff_smoothSupportUnitTangent :
    ContDiff ℝ ∞ smoothSupportUnitTangent := by sorry
