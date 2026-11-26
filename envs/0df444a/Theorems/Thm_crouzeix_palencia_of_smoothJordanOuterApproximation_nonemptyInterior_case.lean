-- Prove2me | Theorems.Thm_crouzeix_palencia_of_smoothJordanOuterApproximation_nonemptyInterior_case
-- name    : crouzeix_palencia_of_smoothJordanOuterApproximation_nonemptyInterior_case
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:55:47.375395+00:00
-- url     : https://prove2.me/theorems/0981ca25-d737-424e-90f0-dfce9fbb8bf3
-- title:
--   crouzeix palencia of smooth Jordan Outer Approximation nonempty Interior case: crouzeix palencia of smooth Jordan Outer Approximation nonempty Interior case
-- statement:
--   To obtain the exact Crouzeix--Palencia bound, the remaining planar
--   geometry theorem may be restricted to compact convex sets with nonempty
--   interior.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanOuterApproximationReduction.lean#L54-L76
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanOuterApproximationReduction.lean#L54-L76

import Definitions.Def_Operator_Crouzeix_SmoothJordanOuterApproximation
import Definitions.Def_Operator_Crouzeix_SmoothJordanOuterApproximationReduction
set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]

theorem crouzeix_palencia_of_smoothJordanOuterApproximation_nonemptyInterior_case
    (A : E →L[ℂ] E)
    (hfull : ∀ K : Set ℂ, IsCompact K → Convex ℝ K →
      (interior K).Nonempty → HasSmoothJordanOuterApproximation K) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
