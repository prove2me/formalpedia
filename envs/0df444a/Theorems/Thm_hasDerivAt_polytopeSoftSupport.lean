-- Prove2me | Theorems.Thm_hasDerivAt_polytopeSoftSupport
-- name    : hasDerivAt_polytopeSoftSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:59:53.593871+00:00
-- url     : https://prove2.me/theorems/23093206-3729-5c8e-885a-d1b8eae3a5d4
-- title:
--   has Deriv At polytope Soft Support: has Deriv At polytope Soft Support
-- statement:
--   Exact first derivative of the log-sum-exp support.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L158-L167
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L158-L167

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem hasDerivAt_polytopeSoftSupport
    {u : Finset ℂ} (hu : u.Nonempty) (delta theta : ℝ) :
    HasDerivAt (polytopeSoftSupport u delta)
      (polytopeSoftSupportFirst u delta theta) theta := by sorry
