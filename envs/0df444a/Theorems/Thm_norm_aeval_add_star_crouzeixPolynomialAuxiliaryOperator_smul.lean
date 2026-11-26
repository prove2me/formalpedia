-- Prove2me | Theorems.Thm_norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_smul
-- name    : norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_smul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:38:03.439655+00:00
-- url     : https://prove2.me/theorems/7d70e808-63d5-4afc-9333-8de170866b2c
-- title:
--   norm aeval add star crouzeix Polynomial Auxiliary Operator smul: norm aeval add star crouzeix Polynomial Auxiliary Operator smul
-- statement:
--   The symmetrized auxiliary expression is homogeneous in norm.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L277-L284
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L277-L284

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

theorem norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_smul
    (A : H →L[ℂ] H) (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) :
    ‖Polynomial.aeval A (a • p) +
        star (crouzeixPolynomialAuxiliaryOperator A Omega (a • p))‖ =
      ‖a‖ * ‖Polynomial.aeval A p +
        star (crouzeixPolynomialAuxiliaryOperator A Omega p)‖ := by sorry
