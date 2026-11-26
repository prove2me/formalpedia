-- Prove2me | Theorems.Thm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_smul
-- name    : aeval_add_star_crouzeixPolynomialAuxiliaryOperator_smul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:37:59.544901+00:00
-- url     : https://prove2.me/theorems/6a967623-fe7b-48d2-a27b-b6666e8fe0b2
-- title:
--   aeval add star crouzeix Polynomial Auxiliary Operator smul: aeval add star crouzeix Polynomial Auxiliary Operator smul
-- statement:
--   Scaling a polynomial scales the symmetrized auxiliary expression by the
--   same complex scalar.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L255-L262
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L255-L262

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
variable [CompleteSpace H]

theorem aeval_add_star_crouzeixPolynomialAuxiliaryOperator_smul
    (A : H →L[ℂ] H) (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) :
    Polynomial.aeval A (a • p) +
        star (crouzeixPolynomialAuxiliaryOperator A Omega (a • p)) =
      a • (Polynomial.aeval A p +
        star (crouzeixPolynomialAuxiliaryOperator A Omega p)) := by sorry
