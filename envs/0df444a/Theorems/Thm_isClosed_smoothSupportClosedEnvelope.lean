-- Prove2me | Theorems.Thm_isClosed_smoothSupportClosedEnvelope
-- name    : isClosed_smoothSupportClosedEnvelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:03:48.571008+00:00
-- url     : https://prove2.me/theorems/d5d052e5-c5ea-41e7-8bfb-a06cedc909ea
-- title:
--   is Closed smooth Support Closed Envelope: is Closed smooth Support Closed Envelope
-- statement:
--   The closed support envelope is closed.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelope.lean#L55-L61
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelope.lean#L55-L61

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
set_option autoImplicit false
open Complex Metric Set
open scoped ComplexConjugate

theorem isClosed_smoothSupportClosedEnvelope (h : ℝ → ℝ) :
    IsClosed (smoothSupportClosedEnvelope h) := by sorry
