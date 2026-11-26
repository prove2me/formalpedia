-- Prove2me | Theorems.Thm_polytopeDirectionalValue_le_add_dist
-- name    : polytopeDirectionalValue_le_add_dist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:07:38.544651+00:00
-- url     : https://prove2.me/theorems/09f42deb-6099-5152-9ad2-17c5f797b515
-- title:
--   polytope Directional Value le add dist: polytope Directional Value le add dist
-- statement:
--   A unit directional functional changes by at most the ambient distance.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelope.lean#L91-L117
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportEnvelope.lean#L91-L117

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
set_option autoImplicit false
open Complex Metric Set
open scoped ComplexConjugate

theorem polytopeDirectionalValue_le_add_dist
    (z w : ℂ) (theta : ℝ) :
    polytopeDirectionalValue w theta ≤
      polytopeDirectionalValue z theta + dist w z := by sorry
