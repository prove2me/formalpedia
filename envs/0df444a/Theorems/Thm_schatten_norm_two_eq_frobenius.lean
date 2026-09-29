-- Prove2me | Theorems.Thm_schatten_norm_two_eq_frobenius
-- name    : schatten_norm_two_eq_frobenius
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-23T17:48:53.905972+00:00
-- url     : https://prove2.me/theorems/f410c35b-20be-48ce-914d-ed5a16dcfd13
-- statement:
--   The Schatten $2$-norm equals the Frobenius norm: $\|X\|_{S_2} = \|X\|_F = (\sum_{i,j} X_{ij}^2)^{1/2}$. Equivalently $\sum_k \sigma_k(X)^2 = \|X\|_F^2$ (sum of squared singular values = sum of squared entries = trace of $X^* X$). Stated by Candès–Recht 2009 §6.1 ("the Frobenius norm is equal to the Schatten 2-norm"); the engine identity behind the even-integer trace-moment proof of the noncommutative Khintchine inequality.
-- source:
--   Candès–Recht 2009 (arXiv:0805.4471), §6.1 lines 1633-1635.

import Definitions.Def_matrix_completion_schatten
import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem schatten_norm_two_eq_frobenius (n1 n2 : Nat) (X : MatrixCompletion.RealMatrix n1 n2) : MatrixCompletion.schattenNorm 2 X = MatrixCompletion.frobeniusNorm X := by sorry
