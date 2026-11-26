-- Prove2me | Theorems.Thm_deriv_deriv_polytopeSoftSupport
-- name    : deriv_deriv_polytopeSoftSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:00:06.005222+00:00
-- url     : https://prove2.me/theorems/acc9cd3d-3bda-5c10-82d6-4b6901876aa8
-- title:
--   deriv deriv polytope Soft Support: deriv deriv polytope Soft Support
-- statement:
--   Second derivative as an equality involving the iterated `deriv`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L201-L210
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L201-L210

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem deriv_deriv_polytopeSoftSupport
    {u : Finset ℂ} (hu : u.Nonempty) (delta theta : ℝ) :
    deriv (deriv (polytopeSoftSupport u delta)) theta =
      polytopeSoftSupportSecond u delta theta := by sorry
