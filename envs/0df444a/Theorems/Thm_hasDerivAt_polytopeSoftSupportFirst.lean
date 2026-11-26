-- Prove2me | Theorems.Thm_hasDerivAt_polytopeSoftSupportFirst
-- name    : hasDerivAt_polytopeSoftSupportFirst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:59:56.539794+00:00
-- url     : https://prove2.me/theorems/49bd128e-6932-51ae-8730-c7d93bef8285
-- title:
--   has Deriv At polytope Soft Support First: has Deriv At polytope Soft Support First
-- statement:
--   Exact derivative of the first-support-derivative formula.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L170-L191
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L170-L191

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem hasDerivAt_polytopeSoftSupportFirst
    {u : Finset ℂ} (hu : u.Nonempty) (delta theta : ℝ) :
    HasDerivAt (polytopeSoftSupportFirst u delta)
      (polytopeSoftSupportSecond u delta theta) theta := by sorry
