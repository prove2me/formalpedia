-- Prove2me | Theorems.Thm_polytopeDirectionalValue_smoothSupportCurve
-- name    : polytopeDirectionalValue_smoothSupportCurve
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:07:01.129198+00:00
-- url     : https://prove2.me/theorems/2f4c2a3f-6d66-5141-9921-f08d3a15db40
-- title:
--   polytope Directional Value smooth Support Curve: polytope Directional Value smooth Support Curve
-- statement:
--   The projection of the support curve onto a normal at `theta`, written in
--   normal/tangent coordinates at `phi`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean#L19-L30
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean#L19-L30

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff

theorem polytopeDirectionalValue_smoothSupportCurve
    (h : ℝ → ℝ) (theta phi : ℝ) :
    polytopeDirectionalValue (smoothSupportCurve h phi) theta =
      h phi * Real.cos (theta - phi) +
        deriv h phi * Real.sin (theta - phi) := by sorry
