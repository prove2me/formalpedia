-- Prove2me | Theorems.Thm_frontier_smoothSupportOpenEnvelope_subset_range_smoothSupportCurve
-- name    : frontier_smoothSupportOpenEnvelope_subset_range_smoothSupportCurve
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:12:01.995779+00:00
-- url     : https://prove2.me/theorems/eeca5628-f693-54f0-8c3c-a84c0b86c629
-- title:
--   frontier smooth Support Open Envelope subset range smooth Support Curve: frontier smooth Support Open Envelope subset range smooth Support Curve
-- statement:
--   For a smooth periodic support function, every frontier point of its open
--   support envelope is hit by the support curve.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveRange.lean#L173-L191
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveRange.lean#L173-L191

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff

theorem frontier_smoothSupportOpenEnvelope_subset_range_smoothSupportCurve
    {h : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ h)
    (hperiodic : Function.Periodic h (2 * Real.pi)) :
    frontier (smoothSupportOpenEnvelope h) ⊆ range (smoothSupportCurve h) := by sorry
