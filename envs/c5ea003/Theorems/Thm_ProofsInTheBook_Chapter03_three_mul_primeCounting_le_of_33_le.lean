-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_three_mul_primeCounting_le_of_33_le
-- name    : ProofsInTheBook.Chapter03.three_mul_primeCounting_le_of_33_le
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:36:46.849518+00:00
-- url     : https://prove2.me/theorems/9ac00767-cf7f-4d7f-9c1c-553d8805cce5
-- title:
--   At most k/3 primes up to k for k at least 33
-- statement:
--   Let $k\in\mathbb N$ with $33\le k$. Write $\pi(t)=|\{p\in\mathbb N:p\le t\text{ and }p\text{ is prime}\}|$. Then
--   $$3\pi(k)\le k.$$
--
--   This prime-counting estimate is used to simplify the logarithmic upper bounds.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 3, “Binomial coefficients are (almost) never powers”, pp. 15–18 (https://doi.org/10.1007/978-3-662-57265-8_3). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L874. The chapter citation identifies the development’s topic; this technical helper is not asserted to be a separately named theorem in the book.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.three_mul_primeCounting_le_of_33_le {k : ℕ} (hk33 : 33 ≤ k) :
    3 * Nat.primeCounting k ≤ k := by sorry
