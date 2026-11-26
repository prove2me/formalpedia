-- Prove2me | Theorems.Thm_convex_smoothSupportClosedEnvelope
-- name    : convex_smoothSupportClosedEnvelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:03:46.17317+00:00
-- url     : https://prove2.me/theorems/ab2b9386-3e45-5349-8eca-0eaf2b1e259d
-- title:
--   convex smooth Support Closed Envelope: convex smooth Support Closed Envelope
-- statement:
--   The closed support envelope is convex.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelope.lean#L64-L71
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelope.lean#L64-L71

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
set_option autoImplicit false
open Complex Metric Set
open scoped ComplexConjugate

theorem convex_smoothSupportClosedEnvelope (h : ℝ → ℝ) :
    Convex ℝ (smoothSupportClosedEnvelope h) := by sorry
