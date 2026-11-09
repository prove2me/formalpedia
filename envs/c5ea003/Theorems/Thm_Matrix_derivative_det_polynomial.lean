-- Prove2me | Theorems.Thm_Matrix_derivative_det_polynomial
-- name    : Matrix.derivative_det_polynomial
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:57:07.318197+00:00
-- url     : https://prove2.me/theorems/6d812d29-993e-4523-8551-d66635e58769
-- title:
--   Polynomial matrix Jacobi formula
-- statement:
--   Let matrices be square on a finite index set over a commutative ring $R$. For $M(X)$ with polynomial entries and entrywise derivative $M\prime(X)$,
--
--   $$\frac{d}{dX}\det M(X)=\operatorname{tr}(M\prime(X)\operatorname{adj}M(X)).$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/1483e8ae3e5491ee176364fe944c90c4341d40ff/research/correspondants_20261013/lean/PolynomialJacobi.lean#L16-L43, lines 16–43; source file SHA-256 9f05f98f965a0100651cade5bd4826f50af073a9e71eb72ae472cdc0ba6092e3; theorem Matrix.derivative_det_polynomial

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

open Finset Polynomial Matrix

namespace Matrix

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

theorem derivative_det_polynomial (M : Matrix n n R[X]) :
    derivative M.det = trace (M.map derivative * M.adjugate) := by sorry







end Matrix
