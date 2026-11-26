-- Prove2me | Theorems.Thm_mem_smoothSupportOpenEnvelope_of_forall_lt
-- name    : mem_smoothSupportOpenEnvelope_of_forall_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:12:16.529602+00:00
-- url     : https://prove2.me/theorems/88dbb426-40a1-4447-b56d-9752e5c56b8c
-- title:
--   mem smooth Support Open Envelope of forall lt: mem smooth Support Open Envelope of forall lt
-- statement:
--   If every support inequality is strict for a continuous periodic support
--   function, then the point lies in the open support envelope.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveRange.lean#L104-L145
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveRange.lean#L104-L145

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff

theorem mem_smoothSupportOpenEnvelope_of_forall_lt
    {h : ℝ → ℝ} (hcontinuous : Continuous h)
    (hperiodic : Function.Periodic h (2 * Real.pi)) {z : ℂ}
    (hz : ∀ theta, polytopeDirectionalValue z theta < h theta) :
    z ∈ smoothSupportOpenEnvelope h := by sorry
