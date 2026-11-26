-- Prove2me | Theorems.Thm_natDegree_crouzeixProductRemainderPolynomial_smul
-- name    : natDegree_crouzeixProductRemainderPolynomial_smul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:33:41.070865+00:00
-- url     : https://prove2.me/theorems/a2efd04f-a56d-4dc8-9ab8-74534dc94ff1
-- title:
--   nat Degree crouzeix Product Remainder Polynomial smul: nat Degree crouzeix Product Remainder Polynomial smul
-- statement:
--   Scaling by a nonzero scalar preserves the natural degree of the
--   product-remainder polynomial.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L400-L405
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L400-L405

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem natDegree_crouzeixProductRemainderPolynomial_smul
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) (ha : a ≠ 0) :
    (crouzeixProductRemainderPolynomial Omega (a • p)).natDegree =
      (crouzeixProductRemainderPolynomial Omega p).natDegree := by sorry
