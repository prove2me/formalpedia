-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_mul_log_sub_mul_log_le_log_choose
-- name    : ProofsInTheBook.Chapter03.mul_log_sub_mul_log_le_log_choose
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T16:27:20.484357+00:00
-- url     : https://prove2.me/theorems/f7589a6b-9b8b-4119-b82e-040c338775f3
-- title:
--   A logarithmic lower bound for a binomial coefficient
-- statement:
--   Let $n,k\in\mathbb N$ satisfy $0<k\le n$. Then
--   $$k\log n-k\log k\le\log\binom nk.$$
--   All logarithms are natural, and the integer quantities are cast to real numbers.
--
--   This is the logarithmic form of the lower estimate $n^k\le k^k\binom nk$.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 3, “Binomial coefficients are (almost) never powers”, pp. 15–18 (https://doi.org/10.1007/978-3-662-57265-8_3). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L485. The chapter citation identifies the development’s topic; this technical helper is not asserted to be a separately named theorem in the book.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.mul_log_sub_mul_log_le_log_choose {n k : ℕ}
    (hkpos : 0 < k) (hkn : k ≤ n) :
    (k : ℝ) * Real.log n - (k : ℝ) * Real.log k ≤ Real.log (n.choose k) := by sorry
