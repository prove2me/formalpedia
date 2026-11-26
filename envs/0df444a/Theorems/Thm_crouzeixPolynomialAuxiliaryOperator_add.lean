-- Prove2me | Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_add
-- name    : crouzeixPolynomialAuxiliaryOperator_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:48:22.150738+00:00
-- url     : https://prove2.me/theorems/9688c561-1ef2-4faf-928e-c534ce9b4bc0
-- title:
--   crouzeix Polynomial Auxiliary Operator add: crouzeix Polynomial Auxiliary Operator add
-- statement:
--   On a contour contained in the resolvent set, the polynomial auxiliary
--   operator is additive in its polynomial argument.  Together with scalar
--   homogeneity below, this records its conjugate-linear dependence on boundary
--   polynomial data.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L210-L227
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L210-L227

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

theorem crouzeixPolynomialAuxiliaryOperator_add
    (A : H →L[ℂ] H) (Omega : SmoothJordanDomain) (p q : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    crouzeixPolynomialAuxiliaryOperator A Omega (p + q) =
      crouzeixPolynomialAuxiliaryOperator A Omega p +
        crouzeixPolynomialAuxiliaryOperator A Omega q := by sorry
