-- Prove2me | Theorems.Thm_smoothSupportCurve_not_mem_smoothSupportOpenEnvelope
-- name    : smoothSupportCurve_not_mem_smoothSupportOpenEnvelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:10:51.460701+00:00
-- url     : https://prove2.me/theorems/e67ee713-911e-4e53-b262-c9f2e00ef87a
-- title:
--   smooth Support Curve not mem smooth Support Open Envelope: smooth Support Curve not mem smooth Support Open Envelope
-- statement:
--   A support-curve point cannot lie in the interior of its prescribed closed
--   support envelope: moving a short distance in its outward normal direction
--   violates the active halfspace.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean#L280-L310
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveGlobal.lean#L280-L310

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff

theorem smoothSupportCurve_not_mem_smoothSupportOpenEnvelope
    (h : ℝ → ℝ) (theta : ℝ) :
    smoothSupportCurve h theta ∉ smoothSupportOpenEnvelope h := by sorry
