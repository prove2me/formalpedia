-- Prove2me | Theorems.Thm_hasDerivAt_polytopeSoftPartitionFirst
-- name    : hasDerivAt_polytopeSoftPartitionFirst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:00:00.767846+00:00
-- url     : https://prove2.me/theorems/973b4f97-d2c6-5c2d-8fba-df12e457cacc
-- title:
--   has Deriv At polytope Soft Partition First: has Deriv At polytope Soft Partition First
-- statement:
--   Exact second derivative of the finite exponential partition.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L146-L155
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L146-L155

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem hasDerivAt_polytopeSoftPartitionFirst
    (u : Finset ℂ) (delta theta : ℝ) :
    HasDerivAt (polytopeSoftPartitionFirst u delta)
      (polytopeSoftPartitionSecond u delta theta) theta := by sorry
