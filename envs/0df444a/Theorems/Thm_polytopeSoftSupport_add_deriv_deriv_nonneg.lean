-- Prove2me | Theorems.Thm_polytopeSoftSupport_add_deriv_deriv_nonneg
-- name    : polytopeSoftSupport_add_deriv_deriv_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:23:05.763065+00:00
-- url     : https://prove2.me/theorems/c1b6e30c-273f-5c0a-9c5a-198b131e35d7
-- title:
--   polytope Soft Support add deriv deriv nonneg: polytope Soft Support add deriv deriv nonneg
-- statement:
--   The actual iterated derivative form of nonnegative soft-support
--   curvature.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L334-L340
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L334-L340

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem polytopeSoftSupport_add_deriv_deriv_nonneg
    {u : Finset ℂ} (hu : u.Nonempty) {delta : ℝ} (hdelta : 0 < delta)
    (theta : ℝ) :
    0 ≤ polytopeSoftSupport u delta theta +
      deriv (deriv (polytopeSoftSupport u delta)) theta := by sorry
