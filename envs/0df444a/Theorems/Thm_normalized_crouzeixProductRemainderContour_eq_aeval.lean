-- Prove2me | Theorems.Thm_normalized_crouzeixProductRemainderContour_eq_aeval
-- name    : normalized_crouzeixProductRemainderContour_eq_aeval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:43:23.189814+00:00
-- url     : https://prove2.me/theorems/6bc1bbcc-19b1-5929-986d-b01f7e5c7c33
-- title:
--   normalized crouzeix Product Remainder Contour eq aeval: normalized crouzeix Product Remainder Contour eq aeval
-- statement:
--   The normalized divided-difference remainder contour is exactly the
--   evaluation at `A` of `crouzeixProductRemainderPolynomial`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L478-L491
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L478-L491

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem normalized_crouzeixProductRemainderContour_eq_aeval
    [CompleteSpace E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
        contourIntegral
          (fun z => star (Polynomial.eval z p) •
            Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)))
          Omega.boundaryParam =
      Polynomial.aeval A (crouzeixProductRemainderPolynomial Omega p) := by sorry
