-- Prove2me | Theorems.Thm_polynomialSupNorm_crouzeixProductRemainderPolynomial_smul
-- name    : polynomialSupNorm_crouzeixProductRemainderPolynomial_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:33:36.41297+00:00
-- url     : https://prove2.me/theorems/50d92d52-23d2-5687-928e-cce8dcf91366
-- title:
--   polynomial Sup Norm crouzeix Product Remainder Polynomial smul: polynomial Sup Norm crouzeix Product Remainder Polynomial smul
-- statement:
--   The product-remainder polynomial has degree-two homogeneity in polynomial
--   sup norm on every control set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L391-L396
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L391-L396

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem polynomialSupNorm_crouzeixProductRemainderPolynomial_smul
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) (K : Set ℂ) :
    polynomialSupNorm (crouzeixProductRemainderPolynomial Omega (a • p)) K =
      ‖a‖ ^ 2 * polynomialSupNorm (crouzeixProductRemainderPolynomial Omega p) K := by sorry
