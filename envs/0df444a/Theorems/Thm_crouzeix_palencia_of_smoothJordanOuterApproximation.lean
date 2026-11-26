-- Prove2me | Theorems.Thm_crouzeix_palencia_of_smoothJordanOuterApproximation
-- name    : crouzeix_palencia_of_smoothJordanOuterApproximation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:53:33.147993+00:00
-- url     : https://prove2.me/theorems/b34fca27-1043-58dc-97c5-4213cb296e39
-- title:
--   crouzeix palencia of smooth Jordan Outer Approximation: crouzeix palencia of smooth Jordan Outer Approximation
-- statement:
--   Local smooth outer approximation of the closed numerical range is the
--   remaining geometric input for the exact Crouzeix--Palencia bound.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanOuterApproximation.lean#L222-L237
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanOuterApproximation.lean#L222-L237

import Definitions.Def_Operator_Crouzeix_SmoothJordanMergelyanAssembly
import Definitions.Def_Operator_Crouzeix_SmoothJordanOuterApproximation
set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem crouzeix_palencia_of_smoothJordanOuterApproximation
    (A : E →L[ℂ] E)
    (houter : HasSmoothJordanOuterApproximation
      (closure (numericalRange A))) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
