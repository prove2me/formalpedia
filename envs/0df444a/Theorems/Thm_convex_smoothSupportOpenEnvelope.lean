-- Prove2me | Theorems.Thm_convex_smoothSupportOpenEnvelope
-- name    : convex_smoothSupportOpenEnvelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:09:11.526901+00:00
-- url     : https://prove2.me/theorems/5515e85c-3337-5e9f-8983-aa8b4920e6c0
-- title:
--   convex smooth Support Open Envelope: convex smooth Support Open Envelope
-- statement:
--   The open support envelope is convex.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelope.lean#L79-L81
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelope.lean#L79-L81

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
set_option autoImplicit false
open Complex Metric Set
open scoped ComplexConjugate

theorem convex_smoothSupportOpenEnvelope (h : ℝ → ℝ) :
    Convex ℝ (smoothSupportOpenEnvelope h) := by sorry
