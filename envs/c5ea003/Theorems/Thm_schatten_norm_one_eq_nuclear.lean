-- Prove2me | Theorems.Thm_schatten_norm_one_eq_nuclear
-- name    : schatten_norm_one_eq_nuclear
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-06-23T17:48:33.131142+00:00
-- url     : https://prove2.me/theorems/8a93964a-544f-4ce3-bad0-873a03839f2b
-- statement:
--   The Schatten $1$-norm equals the nuclear norm: $\|X\|_{S_1} = \|X\|_*= \sum_k \sigma_k(X)$. This is the $q=1$ endpoint of the Schatten scale, stated explicitly by Candès–Recht 2009 §6.1 ("the nuclear norm is equal to the Schatten 1-norm").
-- source:
--   Candès–Recht 2009 (arXiv:0805.4471), §6.1 lines 1633-1634.

import Definitions.Def_matrix_completion_schatten
import Definitions.Def_matrix_completion_basic
open MatrixCompletion

theorem schatten_norm_one_eq_nuclear (n1 n2 : Nat) (X : MatrixCompletion.RealMatrix n1 n2) : MatrixCompletion.schattenNorm 1 X = MatrixCompletion.nuclearNorm X := by sorry
