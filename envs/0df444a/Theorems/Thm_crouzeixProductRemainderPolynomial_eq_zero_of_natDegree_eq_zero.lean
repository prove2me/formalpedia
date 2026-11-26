-- Prove2me | Theorems.Thm_crouzeixProductRemainderPolynomial_eq_zero_of_natDegree_eq_zero
-- name    : crouzeixProductRemainderPolynomial_eq_zero_of_natDegree_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:34:00.809276+00:00
-- url     : https://prove2.me/theorems/36f87734-a19c-498c-8bd4-18d8d9a38795
-- title:
--   crouzeix Product Remainder Polynomial eq zero of nat Degree eq zero: crouzeix Product Remainder Polynomial eq zero of nat Degree eq zero
-- statement:
--   A constant polynomial has zero product-remainder polynomial.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L471-L474
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L471-L474

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem crouzeixProductRemainderPolynomial_eq_zero_of_natDegree_eq_zero
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (hp : p.natDegree = 0) :
    crouzeixProductRemainderPolynomial Omega p = 0 := by sorry
