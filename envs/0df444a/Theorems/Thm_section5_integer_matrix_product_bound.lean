-- Prove2me | Theorems.Thm_section5_integer_matrix_product_bound
-- name    : section5_integer_matrix_product_bound
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-26T19:49:05.226841+00:00
-- url     : https://prove2.me/theorems/e8e40957-b813-58a6-8d31-896f41f4409b
-- title:
--   Entry bounds for complex integer matrix multiplication
-- statement:
--   Let A,B be n×n complex integer matrices and let nonnegative integers a,b bound the absolute value of every real and imaginary component of A,B, respectively. Every real and imaginary component of AB obeys $$|\operatorname{Re}(AB)_{ij}|\le2nab,\qquad|\operatorname{Im}(AB)_{ij}|\le2nab.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5IntegerMatrixBounds.lean, lines 23–25.

import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Mathlib
set_option autoImplicit false

theorem section5_integer_matrix_product_bound {n : ℕ}
    (A B : Section5IntegerMatrix n) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : A.Bounded a) (hB : B.Bounded b) : (A.mul B).Bounded (2*n*a*b) := by sorry
