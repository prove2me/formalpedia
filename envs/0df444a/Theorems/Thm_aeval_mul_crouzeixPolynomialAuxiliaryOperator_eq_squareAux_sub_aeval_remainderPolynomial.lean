-- Prove2me | Theorems.Thm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_squareAux_sub_aeval_remainderPolynomial
-- name    : aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_squareAux_sub_aeval_remainderPolynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:43:42.987615+00:00
-- url     : https://prove2.me/theorems/63abb5b5-4da0-4134-af58-217d08fc9795
-- title:
--   aeval mul crouzeix Polynomial Auxiliary Operator eq square Aux sub aeval remainder Polynomial: aeval mul crouzeix Polynomial Auxiliary Operator eq square Aux sub aeval remainder Polynomial
-- statement:
--   The induction-ready product decomposition: `p(A) G` is the auxiliary
--   operator associated to the scalar boundary datum `|p|²`, minus functional
--   calculus of a strictly lower-degree polynomial.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L536-L548
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L536-L548

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem aeval_mul_crouzeixPolynomialAuxiliaryOperator_eq_squareAux_sub_aeval_remainderPolynomial
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    Polynomial.aeval A p * crouzeixPolynomialAuxiliaryOperator A Omega p =
      crouzeixAuxiliaryOperator A Omega
          (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) -
        Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p) := by sorry
