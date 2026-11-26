-- Prove2me | Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_smul
-- name    : crouzeixPolynomialAuxiliaryOperator_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:37:13.431094+00:00
-- url     : https://prove2.me/theorems/f309b196-ec47-594e-9278-b373465d077a
-- title:
--   crouzeix Polynomial Auxiliary Operator smul: crouzeix Polynomial Auxiliary Operator smul
-- statement:
--   The polynomial auxiliary contour operator is conjugate-linear in its
--   polynomial argument.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L237-L249
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L237-L249

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

theorem crouzeixPolynomialAuxiliaryOperator_smul
    (A : H →L[ℂ] H) (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) :
    crouzeixPolynomialAuxiliaryOperator A Omega (a • p) =
      star a • crouzeixPolynomialAuxiliaryOperator A Omega p := by sorry
