-- Prove2me | Theorems.Thm_periodic_polytopeRoundedSupport
-- name    : periodic_polytopeRoundedSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:02:58.238578+00:00
-- url     : https://prove2.me/theorems/718df478-6fb7-5035-b790-c427c363051d
-- title:
--   periodic polytope Rounded Support: periodic polytope Rounded Support
-- statement:
--   The rounded support remains `2*pi`-periodic.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L343-L349
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L343-L349

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem periodic_polytopeRoundedSupport
    (u : Finset ℂ) (delta rho : ℝ) :
    Function.Periodic (polytopeRoundedSupport u delta rho)
      (2 * Real.pi) := by sorry
