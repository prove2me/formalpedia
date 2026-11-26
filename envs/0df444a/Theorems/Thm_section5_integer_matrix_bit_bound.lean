-- Prove2me | Theorems.Thm_section5_integer_matrix_bit_bound
-- name    : section5_integer_matrix_bit_bound
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:57:37.663023+00:00
-- url     : https://prove2.me/theorems/f4239135-9763-538f-9084-8dca5dd55de7
-- title:
--   Bit growth for complex integer matrix powers
-- statement:
--   Let $A$ be an $n\times n$ complex integer matrix represented by integer real and imaginary parts. Let $b,c,k\in\mathbb N$, assume $n\le2^c$, and assume every real and imaginary entry of $A$ has absolute value at most $2^b$. Then
--
--   $$|\operatorname{Re}(A^k)_{ij}|,\ |\operatorname{Im}(A^k)_{ij}|\le2^{k(b+c+1)}\quad\text{for all }i,j.$$
--
--   This bounds register width for exact powered matrix arithmetic, including $k=0$.
-- source:
--   Original auxiliary result for Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5 (formalization support, not an assertion that the paper states this auxiliary lemma verbatim). Exact formalization: Solutions/Section5IntegerMatrixBounds.lean, lines 66–78.

import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Mathlib
import Theorems.Thm_section5_integer_matrix_product_bound
set_option autoImplicit false

theorem section5_integer_matrix_bit_bound {n : ℕ} (A : Section5IntegerMatrix n)
    (b c : ℕ) (hn : n ≤ 2^c) (hA : A.Bounded ((2:ℤ)^b)) (k : ℕ) :
    (A.power k).Bounded ((2:ℤ)^(k*(b+c+1))) := by sorry
