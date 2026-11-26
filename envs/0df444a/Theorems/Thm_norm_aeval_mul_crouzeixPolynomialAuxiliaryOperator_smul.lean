-- Prove2me | Theorems.Thm_norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_smul
-- name    : norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_smul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:37:51.556176+00:00
-- url     : https://prove2.me/theorems/76793d7b-5bf8-54f2-9bf2-0e8e286ef836
-- title:
--   norm aeval mul crouzeix Polynomial Auxiliary Operator smul: norm aeval mul crouzeix Polynomial Auxiliary Operator smul
-- statement:
--   The product with the auxiliary operator is homogeneous of degree two in
--   norm.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L289-L296
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L289-L296

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

theorem norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_smul
    (A : H →L[ℂ] H) (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) :
    ‖Polynomial.aeval A (a • p) *
        crouzeixPolynomialAuxiliaryOperator A Omega (a • p)‖ =
      ‖a‖ ^ 2 *
        ‖Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p‖ := by sorry
