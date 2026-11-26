-- Prove2me | Theorems.Thm_polynomial_auxiliary_bounds_of_normalized
-- name    : polynomial_auxiliary_bounds_of_normalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:48:15.179024+00:00
-- url     : https://prove2.me/theorems/6568d1d3-a8f3-59e2-bc93-616ffeb0268b
-- title:
--   polynomial auxiliary bounds of normalized: polynomial auxiliary bounds of normalized
-- statement:
--   If both sharp auxiliary estimates hold for every polynomial of unit sup
--   norm on `K`, then they hold with the correct homogeneous constants for every
--   polynomial of positive sup norm.  The zero-sup-norm case is deliberately left
--   separate, since it requires geometric information about `K`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L302-L343
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L302-L343

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

theorem polynomial_auxiliary_bounds_of_normalized
    (A : H →L[ℂ] H) (Omega : SmoothJordanDomain) (K : Set ℂ)
    (p : Polynomial ℂ) (hm : 0 < polynomialSupNorm p K)
    (hnormalized : ∀ q : Polynomial ℂ, polynomialSupNorm q K = 1 →
      ‖Polynomial.aeval A q +
        star (crouzeixPolynomialAuxiliaryOperator A Omega q)‖ ≤ 2 ∧
      ‖Polynomial.aeval A q * crouzeixPolynomialAuxiliaryOperator A Omega q‖ ≤ 1) :
    ‖Polynomial.aeval A p + star (crouzeixPolynomialAuxiliaryOperator A Omega p)‖ ≤
        2 * polynomialSupNorm p K ∧
      ‖Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
        polynomialSupNorm p K ^ 2 := by sorry
