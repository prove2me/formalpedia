-- Prove2me | Theorems.Thm_exists_active_direction_of_mem_frontier_smoothSupportOpenEnvelope
-- name    : exists_active_direction_of_mem_frontier_smoothSupportOpenEnvelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:12:23.500676+00:00
-- url     : https://prove2.me/theorems/43892b89-9d37-46da-9fd1-a6a2149e9c33
-- title:
--   exists active direction of mem frontier smooth Support Open Envelope: exists active direction of mem frontier smooth Support Open Envelope
-- statement:
--   Every frontier point of a continuous periodic support envelope activates
--   at least one of its defining support inequalities.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveRange.lean#L149-L169
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveRange.lean#L149-L169

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff

theorem exists_active_direction_of_mem_frontier_smoothSupportOpenEnvelope
    {h : ℝ → ℝ} (hcontinuous : Continuous h)
    (hperiodic : Function.Periodic h (2 * Real.pi)) {z : ℂ}
    (hz : z ∈ frontier (smoothSupportOpenEnvelope h)) :
    ∃ theta, polytopeDirectionalValue z theta = h theta := by sorry
