-- Prove2me | Theorems.Thm_deriv_polytopeDirectionalValue_right
-- name    : deriv_polytopeDirectionalValue_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:11:35.437262+00:00
-- url     : https://prove2.me/theorems/c38907b2-aeb0-4b21-888b-b09fc6eaadd3
-- title:
--   deriv polytope Directional Value right: deriv polytope Directional Value right
-- statement:
--   Angular derivative of the directional value of a fixed planar point.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveRange.lean#L15-L28
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveRange.lean#L15-L28

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff

theorem deriv_polytopeDirectionalValue_right (z : ℂ) (theta : ℝ) :
    deriv (polytopeDirectionalValue z) theta =
      -z.re * Real.sin theta + z.im * Real.cos theta := by sorry
