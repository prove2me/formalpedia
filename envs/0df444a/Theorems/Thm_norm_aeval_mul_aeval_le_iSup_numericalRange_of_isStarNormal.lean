-- Prove2me | Theorems.Thm_norm_aeval_mul_aeval_le_iSup_numericalRange_of_isStarNormal
-- name    : norm_aeval_mul_aeval_le_iSup_numericalRange_of_isStarNormal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:57:52.451719+00:00
-- url     : https://prove2.me/theorems/96d535e5-cd11-4bdb-8b1d-4b854b92f543
-- title:
--   norm aeval mul aeval le i Sup numerical Range of is Star Normal: norm aeval mul aeval le i Sup numerical Range of is Star Normal
-- statement:
--   Products in the polynomial functional calculus of a normal operator
--   satisfy the sharp constant-one bound.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalPolynomialBound.lean#L47-L54
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/NormalPolynomialBound.lean#L47-L54

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

theorem norm_aeval_mul_aeval_le_iSup_numericalRange_of_isStarNormal
    (A : E →L[ℂ] E) [IsStarNormal A] (p q : ℂ[X]) :
    ‖Polynomial.aeval A p * Polynomial.aeval A q‖ ≤
      ⨆ z ∈ numericalRange A,
        ‖Polynomial.eval z p * Polynomial.eval z q‖ := by sorry
