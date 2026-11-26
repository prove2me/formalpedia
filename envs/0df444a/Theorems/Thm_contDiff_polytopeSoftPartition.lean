-- Prove2me | Theorems.Thm_contDiff_polytopeSoftPartition
-- name    : contDiff_polytopeSoftPartition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:58:14.044895+00:00
-- url     : https://prove2.me/theorems/5ca02be1-d90c-4118-9283-f911cefa71d0
-- title:
--   cont Diff polytope Soft Partition: cont Diff polytope Soft Partition
-- statement:
--   The soft partition sum is infinitely differentiable in its angle.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupport.lean#L74-L79
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupport.lean#L74-L79

import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem contDiff_polytopeSoftPartition (u : Finset ℂ) (delta : ℝ) :
    ContDiff ℝ ∞ (polytopeSoftPartition u delta) := by sorry
