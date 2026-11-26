-- Prove2me | Theorems.Thm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_smul
-- name    : aeval_mul_crouzeixPolynomialAuxiliaryOperator_smul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:37:44.518104+00:00
-- url     : https://prove2.me/theorems/0455ef43-5393-50df-b3f1-140a977ef4f4
-- title:
--   aeval mul crouzeix Polynomial Auxiliary Operator smul: aeval mul crouzeix Polynomial Auxiliary Operator smul
-- statement:
--   Scaling a polynomial scales its product with the auxiliary operator by
--   `a * star a`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L267-L274
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L267-L274

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
omit [CompleteSpace H]

theorem aeval_mul_crouzeixPolynomialAuxiliaryOperator_smul
    (A : H →L[ℂ] H) (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) :
    Polynomial.aeval A (a • p) *
        crouzeixPolynomialAuxiliaryOperator A Omega (a • p) =
      (a * star a) •
        (Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p) := by sorry
