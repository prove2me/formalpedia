-- Prove2me | Theorems.Thm_Matrix_derivative_det_one_sub_X_smul
-- name    : Matrix.derivative_det_one_sub_X_smul
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:04:17.303264+00:00
-- url     : https://prove2.me/theorems/5ed3248e-2ca2-4be3-96fa-f290f1ce8988
-- title:
--   Derivative of the reversed characteristic determinant
-- statement:
--   Let matrices be square on a finite index set over a commutative ring $R$. For any constant matrix $A$,
--
--   $$\frac{d}{dX}\det(I-XA)=-\operatorname{tr}(A\operatorname{adj}(I-XA)).$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/1483e8ae3e5491ee176364fe944c90c4341d40ff/research/correspondants_20261013/lean/PolynomialJacobi.lean#L55-L64, lines 55–64; source file SHA-256 9f05f98f965a0100651cade5bd4826f50af073a9e71eb72ae472cdc0ba6092e3; theorem Matrix.derivative_det_one_sub_X_smul

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Theorems.Thm_Matrix_derivative_det_polynomial
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

open Finset Polynomial Matrix

namespace Matrix

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

theorem derivative_det_one_sub_X_smul (M : Matrix n n R) :
    derivative (det (1 - (X : R[X]) • M.map C)) =
      - trace (M.map C * adjugate (1 - (X : R[X]) • M.map C)) := by sorry



end Matrix
