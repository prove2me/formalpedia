-- Prove2me | Theorems.Thm_polytopeSoftSupport_add_const_add_second_pos
-- name    : polytopeSoftSupport_add_const_add_second_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:01:23.778519+00:00
-- url     : https://prove2.me/theorems/15fb101f-974b-5a88-b64e-b58426a508e5
-- title:
--   polytope Soft Support add const add second pos: polytope Soft Support add const add second pos
-- statement:
--   Adding any positive constant to the soft support makes its support-curve
--   curvature radius strictly positive.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L324-L330
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L324-L330

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem polytopeSoftSupport_add_const_add_second_pos
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) (theta : ℝ) :
    0 < (polytopeSoftSupport u delta theta + rho) +
      polytopeSoftSupportSecond u delta theta := by sorry
