-- Prove2me | Theorems.Thm_closure_convexThickeningApprox_succ_subset
-- name    : closure_convexThickeningApprox_succ_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:44:17.445058+00:00
-- url     : https://prove2.me/theorems/659b3d5c-714e-539c-b23a-2700008acc41
-- title:
--   closure convex Thickening Approx succ subset: closure convex Thickening Approx succ subset
-- statement:
--   The closure of each later open thickening is contained in the preceding
--   open thickening.  Thus the explicit metric approximation has strict adjacent
--   nesting, not merely antitonicity.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothApprox.lean#L85-L94
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothApprox.lean#L85-L94

import Mathlib.Analysis.Convex.Strict
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_SmoothApprox
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff

theorem closure_convexThickeningApprox_succ_subset (K : Set ℂ) (n : ℕ) :
    closure (convexThickeningApprox K (n + 1)) ⊆
      convexThickeningApprox K n := by sorry
