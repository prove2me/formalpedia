-- Prove2me | Theorems.Thm_crouzeixProductRemainderPolynomial_smul
-- name    : crouzeixProductRemainderPolynomial_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:40:36.297598+00:00
-- url     : https://prove2.me/theorems/35b7da9d-efcb-4df0-a103-d0e4a7ce4d6a
-- title:
--   crouzeix Product Remainder Polynomial smul: crouzeix Product Remainder Polynomial smul
-- statement:
--   Scaling `p` by `a` scales its product-remainder polynomial by
--   `star a * a`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L329-L377
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L329-L377

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem crouzeixProductRemainderPolynomial_smul
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) :
    crouzeixProductRemainderPolynomial Omega (a • p) =
      (star a * a) • crouzeixProductRemainderPolynomial Omega p := by sorry
