-- Prove2me | Theorems.Thm_norm_aeval_crouzeixProductRemainderPolynomial_smul
-- name    : norm_aeval_crouzeixProductRemainderPolynomial_smul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:33:27.19426+00:00
-- url     : https://prove2.me/theorems/118c53a8-0625-5d98-a260-4609c517d152
-- title:
--   norm aeval crouzeix Product Remainder Polynomial smul: norm aeval crouzeix Product Remainder Polynomial smul
-- statement:
--   After evaluation at `A`, the remainder polynomial is homogeneous of
--   degree two in norm.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L381-L387
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L381-L387

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_aeval_crouzeixProductRemainderPolynomial_smul
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) :
    ‖Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega (a • p))‖ =
      ‖a‖ ^ 2 *
        ‖Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p)‖ := by sorry
