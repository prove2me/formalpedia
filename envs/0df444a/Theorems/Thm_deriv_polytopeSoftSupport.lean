-- Prove2me | Theorems.Thm_deriv_polytopeSoftSupport
-- name    : deriv_polytopeSoftSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:00:53.93905+00:00
-- url     : https://prove2.me/theorems/2d0158e3-21f4-412e-98dc-4ca8e0ab3031
-- title:
--   deriv polytope Soft Support: deriv polytope Soft Support
-- statement:
--   First derivative as an equality involving `deriv`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L194-L198
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupportCurvature.lean#L194-L198

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem deriv_polytopeSoftSupport
    {u : Finset ℂ} (hu : u.Nonempty) (delta theta : ℝ) :
    deriv (polytopeSoftSupport u delta) theta =
      polytopeSoftSupportFirst u delta theta := by sorry
