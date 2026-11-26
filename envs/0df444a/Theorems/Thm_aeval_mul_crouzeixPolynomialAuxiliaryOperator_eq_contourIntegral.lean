-- Prove2me | Theorems.Thm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_contourIntegral
-- name    : aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_contourIntegral
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:37:35.566504+00:00
-- url     : https://prove2.me/theorems/d04fea40-f69a-5e71-870c-6daf0417c12e
-- title:
--   aeval mul crouzeix Polynomial Auxiliary Operator eq contour Integral: aeval mul crouzeix Polynomial Auxiliary Operator eq contour Integral
-- statement:
--   Polynomial evaluation at `A` pulls through the normalized auxiliary
--   contour integral.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L136-L148
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L136-L148

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Basic
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_Crouzeix_PalenciaSupport
set_option autoImplicit false
open Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_contourIntegral
    (A : H →L[ℂ] H) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        contourIntegral
          (fun z => Polynomial.aeval A p *
            (star (Polynomial.eval z p) • resolvent A z))
          Omega.boundaryParam := by sorry
