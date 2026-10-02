-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_primorial_eq_mul_primeIntervalProduct
-- name    : ProofsInTheBook.Chapter03.primorial_eq_mul_primeIntervalProduct
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:28:12.135257+00:00
-- url     : https://prove2.me/theorems/9da44bd9-da64-40e7-975b-d7d09cb91d8d
-- title:
--   Splitting a primorial at an intermediate endpoint
-- statement:
--   Let $a,M\in\mathbb N$ with $a\le M$. Define $t\#=\prod_{p\le t,\ p\text{ prime}}p$ and $P(a,M)=\prod_{a<p\le M,\ p\text{ prime}}p$, using empty product $1$. Then
--   $$M\#=(a\#)\,P(a,M).$$
--
--   This finite-product decomposition isolates the contribution of primes in an interval.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 3, “Binomial coefficients are (almost) never powers”, pp. 15–18 (https://doi.org/10.1007/978-3-662-57265-8_3). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L66. The chapter citation identifies the development’s topic; this technical helper is not asserted to be a separately named theorem in the book.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.primorial_eq_mul_primeIntervalProduct {a M : ℕ} (haM : a ≤ M) :
    primorial M = primorial a * primeIntervalProduct a M := by sorry
