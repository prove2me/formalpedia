-- Prove2me | Theorems.Thm_commute_aeval_crouzeixPolynomialAuxiliaryOperator
-- name    : commute_aeval_crouzeixPolynomialAuxiliaryOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:44:59.954905+00:00
-- url     : https://prove2.me/theorems/5afc2854-cf0a-4eea-9ac3-747a07e99ac8
-- title:
--   commute aeval crouzeix Polynomial Auxiliary Operator: commute aeval crouzeix Polynomial Auxiliary Operator
-- statement:
--   Polynomial evaluation at `A` commutes with every polynomial auxiliary
--   contour operator whose boundary lies in the resolvent set of `A`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L176-L204
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L176-L204

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

theorem commute_aeval_crouzeixPolynomialAuxiliaryOperator
    (A : H →L[ℂ] H) (Omega : SmoothJordanDomain) (p q : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    Commute (Polynomial.aeval A p)
      (crouzeixPolynomialAuxiliaryOperator A Omega q) := by sorry
