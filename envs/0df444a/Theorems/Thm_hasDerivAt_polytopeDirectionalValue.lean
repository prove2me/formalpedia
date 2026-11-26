-- Prove2me | Theorems.Thm_hasDerivAt_polytopeDirectionalValue
-- name    : hasDerivAt_polytopeDirectionalValue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:00:04.260478+00:00
-- url     : https://prove2.me/theorems/6fe5aa4e-47af-48a3-95f9-657576006641
-- title:
--   has Deriv At polytope Directional Value: has Deriv At polytope Directional Value
-- statement:
--   First angular derivative of a vertex directional value.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L68-L80
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L68-L80

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem hasDerivAt_polytopeDirectionalValue (z : ℂ) (theta : ℝ) :
    HasDerivAt (polytopeDirectionalValue z)
      (polytopeDirectionalVelocity z theta) theta := by sorry
