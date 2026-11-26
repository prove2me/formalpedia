-- Prove2me | Theorems.Thm_polytopeDirectionalValue_smoothSupportCurve_le
-- name    : polytopeDirectionalValue_smoothSupportCurve_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:10:33.878552+00:00
-- url     : https://prove2.me/theorems/0b55e82c-521d-4f6d-851c-4fbb2f0a5473
-- title:
--   polytope Directional Value smooth Support Curve le: polytope Directional Value smooth Support Curve le
-- statement:
--   A smooth periodic positive-curvature support curve lies in every
--   halfspace prescribed by its support function.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean#L153-L188
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean#L153-L188

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff

theorem polytopeDirectionalValue_smoothSupportCurve_le
    {h : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ h)
    (hperiodic : Function.Periodic h (2 * Real.pi))
    (hcurv : ∀ x, 0 < smoothSupportCurvatureRadius h x)
    (theta phi : ℝ) :
    polytopeDirectionalValue (smoothSupportCurve h phi) theta ≤ h theta := by sorry
