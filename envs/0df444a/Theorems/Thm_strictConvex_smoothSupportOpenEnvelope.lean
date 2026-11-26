-- Prove2me | Theorems.Thm_strictConvex_smoothSupportOpenEnvelope
-- name    : strictConvex_smoothSupportOpenEnvelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:09:19.434826+00:00
-- url     : https://prove2.me/theorems/7d47b5ad-1cf5-52ea-9bf4-8093d835e16c
-- title:
--   strict Convex smooth Support Open Envelope: strict Convex smooth Support Open Envelope
-- statement:
--   In Mathlib's open-set formulation, the open support envelope is strictly
--   convex.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelope.lean#L85-L88
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelope.lean#L85-L88

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
set_option autoImplicit false
open Complex Metric Set
open scoped ComplexConjugate

theorem strictConvex_smoothSupportOpenEnvelope (h : ℝ → ℝ) :
    StrictConvex ℝ (smoothSupportOpenEnvelope h) := by sorry
