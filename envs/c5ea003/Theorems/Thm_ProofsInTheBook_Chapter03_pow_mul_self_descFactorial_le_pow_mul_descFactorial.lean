-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_pow_mul_self_descFactorial_le_pow_mul_descFactorial
-- name    : ProofsInTheBook.Chapter03.pow_mul_self_descFactorial_le_pow_mul_descFactorial
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:27:44.238665+00:00
-- url     : https://prove2.me/theorems/a9ccf512-ef83-44ff-8e50-21e26d545735
-- title:
--   A multiplicative comparison of falling factorials
-- statement:
--   Let $n,k\in\mathbb N$ with $k\le n$, and write $u^{\underline{k}}=\prod_{i=0}^{k-1}(u-i)$, with empty product $1$. Then
--   $$n^k\,k^{\underline{k}}\le k^k\,n^{\underline{k}}.$$
--   The powers and products are natural-number operations, including $0^0=1$.
--
--   This is the product inequality underlying the elementary binomial lower bound.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 3, “Binomial coefficients are (almost) never powers”, pp. 15–18 (https://doi.org/10.1007/978-3-662-57265-8_3). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L340. The chapter citation identifies the development’s topic; this technical helper is not asserted to be a separately named theorem in the book.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.pow_mul_self_descFactorial_le_pow_mul_descFactorial {n k : ℕ} (hkn : k ≤ n) :
    n ^ k * k.descFactorial k ≤ k ^ k * n.descFactorial k := by sorry
