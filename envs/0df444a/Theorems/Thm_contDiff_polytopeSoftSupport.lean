-- Prove2me | Theorems.Thm_contDiff_polytopeSoftSupport
-- name    : contDiff_polytopeSoftSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:58:59.984803+00:00
-- url     : https://prove2.me/theorems/b0bf25ed-b68a-5c6a-b1ab-b2bb13d205f2
-- title:
--   cont Diff polytope Soft Support: cont Diff polytope Soft Support
-- statement:
--   For a nonempty finite point set, the soft support function is infinitely
--   differentiable in its angle.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupport.lean#L83-L88
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupport.lean#L83-L88

import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem contDiff_polytopeSoftSupport {u : Finset ℂ} (hu : u.Nonempty)
    (delta : ℝ) :
    ContDiff ℝ ∞ (polytopeSoftSupport u delta) := by sorry
