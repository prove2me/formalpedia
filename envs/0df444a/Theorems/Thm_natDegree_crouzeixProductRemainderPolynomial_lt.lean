-- Prove2me | Theorems.Thm_natDegree_crouzeixProductRemainderPolynomial_lt
-- name    : natDegree_crouzeixProductRemainderPolynomial_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:33:57.484924+00:00
-- url     : https://prove2.me/theorems/d4bd9b25-3a67-4f83-ba83-a42f1df6b1c5
-- title:
--   nat Degree crouzeix Product Remainder Polynomial lt: nat Degree crouzeix Product Remainder Polynomial lt
-- statement:
--   For a nonconstant `p`, its product-remainder polynomial has strictly
--   smaller degree.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L452-L468
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L452-L468

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem natDegree_crouzeixProductRemainderPolynomial_lt
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (hp : 0 < p.natDegree) :
    (crouzeixProductRemainderPolynomial Omega p).natDegree < p.natDegree := by sorry
