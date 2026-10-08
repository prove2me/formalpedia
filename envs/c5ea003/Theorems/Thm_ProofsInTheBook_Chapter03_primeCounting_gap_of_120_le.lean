-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_primeCounting_gap_of_120_le
-- name    : ProofsInTheBook.Chapter03.primeCounting_gap_of_120_le
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T16:27:30.97683+00:00
-- url     : https://prove2.me/theorems/01e9b1c9-6dbd-4812-b13f-def4d37dab8e
-- title:
--   Fewer than k/2 primes up to k for k at least 120
-- statement:
--   Let $k\in\mathbb N$ with $120\le k$. Write $\pi(t)=|\{p\in\mathbb N:p\le t\text{ and }p\text{ is prime}\}|$. Then
--   $$2\pi(k)<k.$$
--
--   This is a numerical prime-counting estimate at the stated threshold.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 3, “Binomial coefficients are (almost) never powers”, pp. 15–18 (https://doi.org/10.1007/978-3-662-57265-8_3). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L744. The chapter citation identifies the development’s topic; this technical helper is not asserted to be a separately named theorem in the book.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.primeCounting_gap_of_120_le {k : ℕ} (hk : 120 ≤ k) :
    2 * Nat.primeCounting k < k := by sorry
