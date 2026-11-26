-- Prove2me | Theorems.Thm_polytopeDirectionalValue_smoothSupportCurve_self
-- name    : polytopeDirectionalValue_smoothSupportCurve_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:06:19.311917+00:00
-- url     : https://prove2.me/theorems/bc33311d-6017-45f3-a2b7-d7dff4610746
-- title:
--   polytope Directional Value smooth Support Curve self: polytope Directional Value smooth Support Curve self
-- statement:
--   The curve point has the prescribed support value in its own normal
--   direction.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L184-L197
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L184-L197

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem polytopeDirectionalValue_smoothSupportCurve_self
    (h : ℝ → ℝ) (theta : ℝ) :
    polytopeDirectionalValue (smoothSupportCurve h theta) theta = h theta := by sorry
