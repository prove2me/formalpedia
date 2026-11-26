-- Prove2me | Theorems.Thm_periodic_smoothSupportCurve
-- name    : periodic_smoothSupportCurve
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:05:47.273833+00:00
-- url     : https://prove2.me/theorems/98456bf2-e8cb-534a-8365-bba55242cc89
-- title:
--   periodic smooth Support Curve: periodic smooth Support Curve
-- statement:
--   A smooth periodic support function produces a periodic support curve.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L61-L69
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurve.lean#L61-L69

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem periodic_smoothSupportCurve {h : ℝ → ℝ}
    (hperiodic : Function.Periodic h (2 * Real.pi)) :
    Function.Periodic (smoothSupportCurve h) (2 * Real.pi) := by sorry
