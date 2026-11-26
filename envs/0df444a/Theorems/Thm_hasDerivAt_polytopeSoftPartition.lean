-- Prove2me | Theorems.Thm_hasDerivAt_polytopeSoftPartition
-- name    : hasDerivAt_polytopeSoftPartition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:01:13.611108+00:00
-- url     : https://prove2.me/theorems/0382dab0-3a31-444f-acdf-a11408adcbd9
-- title:
--   has Deriv At polytope Soft Partition: has Deriv At polytope Soft Partition
-- statement:
--   Exact first derivative of the finite exponential partition.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L107-L116
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L107-L116

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem hasDerivAt_polytopeSoftPartition
    (u : Finset ℂ) (delta theta : ℝ) :
    HasDerivAt (polytopeSoftPartition u delta)
      (polytopeSoftPartitionFirst u delta theta) theta := by sorry
