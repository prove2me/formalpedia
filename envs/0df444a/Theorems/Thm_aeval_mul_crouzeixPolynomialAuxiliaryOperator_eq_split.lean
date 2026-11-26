-- Prove2me | Theorems.Thm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_split
-- name    : aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:43:15.822707+00:00
-- url     : https://prove2.me/theorems/e48524ec-4a2a-4f94-8a66-fc639bc4f1ba
-- title:
--   aeval mul crouzeix Polynomial Auxiliary Operator eq split: aeval mul crouzeix Polynomial Auxiliary Operator eq split
-- statement:
--   After pulling `p(A)` through the auxiliary contour integral, the
--   pointwise resolvent splitting separates the squared boundary value from the
--   polynomial divided-difference term.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L153-L172
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L153-L172

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

theorem aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_split
    (A : H →L[ℂ] H) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        contourIntegral
          (fun z =>
            (star (Polynomial.eval z p) * Polynomial.eval z p) • resolvent A z -
              star (Polynomial.eval z p) •
                Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)))
          Omega.boundaryParam := by sorry
