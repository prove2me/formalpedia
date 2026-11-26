-- Prove2me | Theorems.Thm_polytopeSoftPartitionSecond_eq_velocitySqMoment_sub_positionMoment
-- name    : polytopeSoftPartitionSecond_eq_velocitySqMoment_sub_positionMoment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:01:23.994527+00:00
-- url     : https://prove2.me/theorems/876b4b4a-f201-4cca-83d7-85d40a54efc6
-- title:
--   polytope Soft Partition Second eq velocity Sq Moment sub position Moment: polytope Soft Partition Second eq velocity Sq Moment sub position Moment
-- statement:
--   The second partition derivative is the square-velocity moment minus the
--   position moment.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L214-L225
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L214-L225

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem polytopeSoftPartitionSecond_eq_velocitySqMoment_sub_positionMoment
    (u : Finset ℂ) (delta theta : ℝ) :
    polytopeSoftPartitionSecond u delta theta =
      polytopeSoftPartitionVelocitySqMoment u delta theta -
        polytopeSoftPartitionPositionMoment u delta theta := by sorry
