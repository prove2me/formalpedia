-- Prove2me | Theorems.Thm_convexThickeningApprox_spec
-- name    : convexThickeningApprox_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:44:22.730886+00:00
-- url     : https://prove2.me/theorems/2cbc2b01-9887-4ed6-b9d4-8ab4b3ab3949
-- title:
--   convex Thickening Approx spec: convex Thickening Approx spec
-- statement:
--   A compact convex planar set is the exact intersection of an explicit
--   sequence of open strictly convex supersets.
--
--   This discharges the containment, convexity, openness, and intersection parts
--   of L4.2b.  The remaining gap is to replace or perturb these thickenings so
--   that every frontier has a smooth regular Jordan parametrization.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothApprox.lean#L128-L140
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothApprox.lean#L128-L140

import Mathlib.Analysis.Convex.Strict
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_SmoothApprox
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff

theorem convexThickeningApprox_spec (K : Set ℂ) (hcompact : IsCompact K)
    (hconvex : Convex ℝ K) :
    (∀ n, K ⊆ convexThickeningApprox K n ∧
      IsOpen (convexThickeningApprox K n) ∧
      StrictConvex ℝ (convexThickeningApprox K n)) ∧
      (⋂ n, convexThickeningApprox K n) = K := by sorry
