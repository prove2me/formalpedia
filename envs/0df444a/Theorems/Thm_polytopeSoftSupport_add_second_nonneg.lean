-- Prove2me | Theorems.Thm_polytopeSoftSupport_add_second_nonneg
-- name    : polytopeSoftSupport_add_second_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:00:52.235337+00:00
-- url     : https://prove2.me/theorems/e8e69f27-8ed4-4e54-9827-2698ce1f5062
-- title:
--   polytope Soft Support add second nonneg: polytope Soft Support add second nonneg
-- statement:
--   The log-sum-exp support has nonnegative support-curve curvature radius
--   `h + h''`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L284-L320
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L284-L320

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem polytopeSoftSupport_add_second_nonneg
    {u : Finset ℂ} (hu : u.Nonempty) {delta : ℝ} (hdelta : 0 < delta)
    (theta : ℝ) :
    0 ≤ polytopeSoftSupport u delta theta +
      polytopeSoftSupportSecond u delta theta := by sorry
