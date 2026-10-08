-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_log_factorial_le_stirling_upper
-- name    : ProofsInTheBook.Chapter03.log_factorial_le_stirling_upper
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T16:26:50.566296+00:00
-- url     : https://prove2.me/theorems/59f31e95-419f-4137-86e9-c6d5a1269b14
-- title:
--   An elementary Stirling upper bound for log factorial
-- statement:
--   Let $m\in\mathbb N$ with $m\ne0$. Then
--   $$\log(m!)\le m\log m-m+\tfrac12\log m+1.$$
--   The logarithm is the natural logarithm, and natural numbers are interpreted as real numbers in the expression.
--
--   This supplies an explicit factorial estimate for the logarithmic comparisons.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 3, “Binomial coefficients are (almost) never powers”, pp. 15–18 (https://doi.org/10.1007/978-3-662-57265-8_3). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L508. The chapter citation identifies the development’s topic; this technical helper is not asserted to be a separately named theorem in the book.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.log_factorial_le_stirling_upper {m : ℕ} (hm : m ≠ 0) :
    Real.log (m !) ≤ (m : ℝ) * Real.log m - (m : ℝ) + Real.log m / 2 + 1 := by sorry
