-- Prove2me | Theorems.Thm_smoothSupportDirectionalLinearMap_apply
-- name    : smoothSupportDirectionalLinearMap_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:03:47.135105+00:00
-- url     : https://prove2.me/theorems/e27a939c-09d6-4375-8def-588be672d5d9
-- title:
--   smooth Support Directional Linear Map apply: smooth Support Directional Linear Map apply
-- statement:
--   The smooth Support Directional Linear Map apply construction uses the smooth Support Directional Linear Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelope.lean#L22-L30
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelope.lean#L22-L30

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
set_option autoImplicit false
open Complex Metric Set
open scoped ComplexConjugate

theorem smoothSupportDirectionalLinearMap_apply
    (theta : ℝ) (z : ℂ) :
    smoothSupportDirectionalLinearMap theta z =
      polytopeDirectionalValue z theta := by sorry
