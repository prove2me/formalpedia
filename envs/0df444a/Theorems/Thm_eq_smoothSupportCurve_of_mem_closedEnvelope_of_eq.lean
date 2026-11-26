-- Prove2me | Theorems.Thm_eq_smoothSupportCurve_of_mem_closedEnvelope_of_eq
-- name    : eq_smoothSupportCurve_of_mem_closedEnvelope_of_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:11:55.531291+00:00
-- url     : https://prove2.me/theorems/db9a781f-cecf-4cbf-b095-9fa11fd97e5b
-- title:
--   eq smooth Support Curve of mem closed Envelope of eq: eq smooth Support Curve of mem closed Envelope of eq
-- statement:
--   If a point of a smooth support envelope activates the inequality in
--   direction `theta`, then it is the corresponding support-curve point.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveRange.lean#L32-L100
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveRange.lean#L32-L100

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff

theorem eq_smoothSupportCurve_of_mem_closedEnvelope_of_eq
    {h : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ h)
    {z : ℂ} (hz : z ∈ smoothSupportClosedEnvelope h) {theta : ℝ}
    (hactive : polytopeDirectionalValue z theta = h theta) :
    z = smoothSupportCurve h theta := by sorry
