-- Prove2me | Theorems.Thm_polytopeSoftPartitionFirst_sq_le_partition_mul_velocitySqMoment
-- name    : polytopeSoftPartitionFirst_sq_le_partition_mul_velocitySqMoment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:02:23.868878+00:00
-- url     : https://prove2.me/theorems/32f580f6-96a2-43d1-91c3-4aadfc148499
-- title:
--   polytope Soft Partition First sq le partition mul velocity Sq Moment: polytope Soft Partition First sq le partition mul velocity Sq Moment
-- statement:
--   Weighted finite Cauchy--Schwarz for the first partition derivative.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L263-L280
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L263-L280

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem polytopeSoftPartitionFirst_sq_le_partition_mul_velocitySqMoment
    (u : Finset ℂ) (delta theta : ℝ) :
    polytopeSoftPartitionFirst u delta theta ^ 2 ≤
      polytopeSoftPartition u delta theta *
        polytopeSoftPartitionVelocitySqMoment u delta theta := by sorry
