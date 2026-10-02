-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_log_primeIntervalProduct_eq_theta_sub
-- name    : ProofsInTheBook.Chapter03.log_primeIntervalProduct_eq_theta_sub
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:27:00.639039+00:00
-- url     : https://prove2.me/theorems/21913ec7-c29f-4fef-a28c-e919d80e29f4
-- title:
--   The logarithm of a prime-interval product is a theta difference
-- statement:
--   Let $a,M\in\mathbb N$ with $a\le M$. Write $P(a,b)=\prod_{a<p\le b,\ p\text{ prime}}p$, with empty product $1$, and $\vartheta(x)=\sum_{p\le x,\ p\text{ prime}}\log p$. Then
--   $$\log P(a,M)=\vartheta(M)-\vartheta(a).$$
--   The endpoints are included only on the right of the interval, and logarithms are natural.
--
--   This converts a finite prime product into an additive Chebyshev-function difference.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 3, “Binomial coefficients are (almost) never powers”, pp. 15–18 (https://doi.org/10.1007/978-3-662-57265-8_3). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L86. The chapter citation identifies the development’s topic; this technical helper is not asserted to be a separately named theorem in the book.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.log_primeIntervalProduct_eq_theta_sub {a M : ℕ} (haM : a ≤ M) :
    Real.log (primeIntervalProduct a M) =
      Chebyshev.theta (M : ℝ) - Chebyshev.theta (a : ℝ) := by sorry
