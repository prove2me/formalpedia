-- Prove2me | Theorems.Thm_periodic_polytopeSoftPartition
-- name    : periodic_polytopeSoftPartition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:57:44.529873+00:00
-- url     : https://prove2.me/theorems/57b6222a-5d34-4dbe-814f-b80b1f74e21d
-- title:
--   periodic polytope Soft Partition: periodic polytope Soft Partition
-- statement:
--   The soft partition sum is `2*pi`-periodic.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupport.lean#L44-L50
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PolytopeSoftSupport.lean#L44-L50

import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
set_option autoImplicit false
open Complex Set
open scoped ContDiff

theorem periodic_polytopeSoftPartition (u : Finset ℂ) (delta : ℝ) :
    Function.Periodic (polytopeSoftPartition u delta) (2 * Real.pi) := by sorry
