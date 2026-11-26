-- Prove2me | Theorems.Thm_hasSmoothJordanOuterApproximation_of_nonemptyInterior_case
-- name    : hasSmoothJordanOuterApproximation_of_nonemptyInterior_case
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:54:52.490977+00:00
-- url     : https://prove2.me/theorems/6fe6b3f3-0ecc-54d1-9b03-167806a3833e
-- title:
--   has Smooth Jordan Outer Approximation of nonempty Interior case: has Smooth Jordan Outer Approximation of nonempty Interior case
-- statement:
--   Smooth outer approximation for compact convex sets with nonempty interior
--   implies the same statement for every nonempty compact convex set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanOuterApproximationReduction.lean#L17-L44
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanOuterApproximationReduction.lean#L17-L44

import Definitions.Def_Operator_Crouzeix_SmoothJordanOuterApproximation
import Definitions.Def_Operator_Crouzeix_SmoothJordanOuterApproximationReduction
set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace

theorem hasSmoothJordanOuterApproximation_of_nonemptyInterior_case
    {K : Set ℂ} (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hKconvex : Convex ℝ K)
    (hfull : ∀ L : Set ℂ, IsCompact L → Convex ℝ L →
      (interior L).Nonempty → HasSmoothJordanOuterApproximation L) :
    HasSmoothJordanOuterApproximation K := by sorry
