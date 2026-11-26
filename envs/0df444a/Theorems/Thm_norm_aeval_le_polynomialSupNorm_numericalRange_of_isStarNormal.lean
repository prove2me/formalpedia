-- Prove2me | Theorems.Thm_norm_aeval_le_polynomialSupNorm_numericalRange_of_isStarNormal
-- name    : norm_aeval_le_polynomialSupNorm_numericalRange_of_isStarNormal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:44:14.301612+00:00
-- url     : https://prove2.me/theorems/adefa0ab-e088-5c5f-b33e-5a66d9c81b0b
-- title:
--   norm aeval le polynomial Sup Norm numerical Range of is Star Normal: norm aeval le polynomial Sup Norm numerical Range of is Star Normal
-- statement:
--   The sharp normal-operator polynomial bound, with the supremum taken
--   directly over the numerical range.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalPolynomialBound.lean#L36-L43
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalPolynomialBound.lean#L36-L43

import Definitions.Def_Operator_Crouzeix_PolynomialBound
import Definitions.Def_Operator_NumericalRange_RadiusNormal
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_NormalPolynomialBound
set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem norm_aeval_le_polynomialSupNorm_numericalRange_of_isStarNormal
    (A : E →L[ℂ] E) [IsStarNormal A] (p : ℂ[X]) :
    ‖Polynomial.aeval A p‖ ≤ polynomialSupNorm p (numericalRange A) := by sorry
