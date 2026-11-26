-- Prove2me | Theorems.Thm_crouzeixProductRemainderPolynomial_add_C
-- name    : crouzeixProductRemainderPolynomial_add_C
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:33:10.676114+00:00
-- url     : https://prove2.me/theorems/6740e201-d303-441d-b2aa-0d98b93f3b55
-- title:
--   crouzeix Product Remainder Polynomial add C: crouzeix Product Remainder Polynomial add C
-- statement:
--   Adding a constant to `p` leaves its product-remainder polynomial
--   unchanged.  The divided difference does not see the constant, while the new
--   cross term is the contour integral of a scalar polynomial and hence vanishes
--   on the closed boundary.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L254-L325
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L254-L325

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem crouzeixProductRemainderPolynomial_add_C
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (a : ℂ) :
    crouzeixProductRemainderPolynomial Omega (p + Polynomial.C a) =
      crouzeixProductRemainderPolynomial Omega p := by sorry
