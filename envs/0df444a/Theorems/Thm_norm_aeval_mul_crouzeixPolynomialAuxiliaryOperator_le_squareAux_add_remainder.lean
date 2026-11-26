-- Prove2me | Theorems.Thm_norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_squareAux_add_remainder
-- name    : norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_squareAux_add_remainder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:34:09.2042+00:00
-- url     : https://prove2.me/theorems/dc6187e3-405e-5be8-9fd4-868ccb18f113
-- title:
--   norm aeval mul crouzeix Polynomial Auxiliary Operator le square Aux add remainder: norm aeval mul crouzeix Polynomial Auxiliary Operator le square Aux add remainder
-- statement:
--   The recursive product decomposition reduces its norm to the norm of the
--   scalar-square auxiliary operator plus the lower-degree functional calculus
--   term.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L553-L565
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L553-L565

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_squareAux_add_remainder
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    ‖Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
      ‖crouzeixAuxiliaryOperator A Omega
        (fun z => star (Polynomial.eval z p) * Polynomial.eval z p)‖ +
      ‖Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p)‖ := by sorry
