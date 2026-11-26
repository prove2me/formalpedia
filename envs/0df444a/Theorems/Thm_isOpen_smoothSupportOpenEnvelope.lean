-- Prove2me | Theorems.Thm_isOpen_smoothSupportOpenEnvelope
-- name    : isOpen_smoothSupportOpenEnvelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:05:51.259611+00:00
-- url     : https://prove2.me/theorems/54d04bef-9793-558a-abf0-f682e6b44c12
-- title:
--   is Open smooth Support Open Envelope: is Open smooth Support Open Envelope
-- statement:
--   The open support envelope is open.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelope.lean#L74-L76
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelope.lean#L74-L76

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
set_option autoImplicit false
open Complex Metric Set
open scoped ComplexConjugate

theorem isOpen_smoothSupportOpenEnvelope (h : ℝ → ℝ) :
    IsOpen (smoothSupportOpenEnvelope h) := by sorry
