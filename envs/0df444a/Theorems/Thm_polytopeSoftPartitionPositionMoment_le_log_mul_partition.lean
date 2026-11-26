-- Prove2me | Theorems.Thm_polytopeSoftPartitionPositionMoment_le_log_mul_partition
-- name    : polytopeSoftPartitionPositionMoment_le_log_mul_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:01:20.457445+00:00
-- url     : https://prove2.me/theorems/1f643601-8086-4cf8-873c-5c9fb6786102
-- title:
--   polytope Soft Partition Position Moment le log mul partition: polytope Soft Partition Position Moment le log mul partition
-- statement:
--   The weighted position moment is at most the log partition times the
--   partition mass.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L229-L260
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L229-L260

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem polytopeSoftPartitionPositionMoment_le_log_mul_partition
    {u : Finset ℂ} (_hu : u.Nonempty) {delta : ℝ} (_hdelta : 0 < delta)
    (theta : ℝ) :
    polytopeSoftPartitionPositionMoment u delta theta ≤
      polytopeSoftPartition u delta theta *
        Real.log (polytopeSoftPartition u delta theta) := by sorry
