-- Prove2me | Theorems.Thm_smoothSupportClosedEnvelope_eq_iInter
-- name    : smoothSupportClosedEnvelope_eq_iInter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:03:52.825979+00:00
-- url     : https://prove2.me/theorems/6a3f0a5d-afb6-4de3-a174-d80b5b7acc96
-- title:
--   smooth Support Closed Envelope eq i Inter: smooth Support Closed Envelope eq i Inter
-- statement:
--   The support envelope as an explicit intersection of halfspaces.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelope.lean#L41-L45
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelope.lean#L41-L45

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
set_option autoImplicit false
open Complex Metric Set
open scoped ComplexConjugate

theorem smoothSupportClosedEnvelope_eq_iInter (h : ℝ → ℝ) :
    smoothSupportClosedEnvelope h =
      ⋂ theta : ℝ, {z : ℂ | polytopeDirectionalValue z theta ≤ h theta} := by sorry
