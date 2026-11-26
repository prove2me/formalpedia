-- Prove2me | Theorems.Thm_continuous_polytopeDirectionalValue_left
-- name    : continuous_polytopeDirectionalValue_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:09:48.232966+00:00
-- url     : https://prove2.me/theorems/68663ac7-24f1-49c5-9ec9-cbfaf846423d
-- title:
--   continuous polytope Directional Value left: continuous polytope Directional Value left
-- statement:
--   Each directional-value function is continuous in the planar point.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelope.lean#L48-L52
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelope.lean#L48-L52

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
set_option autoImplicit false
open Complex Metric Set
open scoped ComplexConjugate

theorem continuous_polytopeDirectionalValue_left (theta : ℝ) :
    Continuous (fun z : ℂ => polytopeDirectionalValue z theta) := by sorry
