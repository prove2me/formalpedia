-- Prove2me | Theorems.Thm_periodic_polytopeSoftSupport
-- name    : periodic_polytopeSoftSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:59:07.532313+00:00
-- url     : https://prove2.me/theorems/b3ee9b1d-787e-43ef-b4cf-06e98c22d2da
-- title:
--   periodic polytope Soft Support: periodic polytope Soft Support
-- statement:
--   The soft support function is `2*pi`-periodic.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupport.lean#L53-L57
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupport.lean#L53-L57

import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem periodic_polytopeSoftSupport (u : Finset ℂ) (delta : ℝ) :
    Function.Periodic (polytopeSoftSupport u delta) (2 * Real.pi) := by sorry
