-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_pow_gap_small_k_tail
-- name    : ProofsInTheBook.Chapter03.pow_gap_small_k_tail
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:27:32.313164+00:00
-- url     : https://prove2.me/theorems/4407331e-956b-4fc6-8711-325956da6e68
-- title:
--   A power gap for k from 1 to 8 and n at least 94
-- statement:
--   Let $n,k\in\mathbb N$ satisfy $0<k<9$ and $94\le n$. Write $\pi(t)=|\{p\in\mathbb N:p\le t\text{ and }p\text{ is prime}\}|$. Then
--   $$k^k<n^{\,k-\pi(k)}.$$
--   The exponent uses natural subtraction, truncated at zero.
--
--   This is a small-k numerical tail estimate.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 3, “Binomial coefficients are (almost) never powers”, pp. 15–18 (https://doi.org/10.1007/978-3-662-57265-8_3). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L2203. The chapter citation identifies the development’s topic; this technical helper is not asserted to be a separately named theorem in the book.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.pow_gap_small_k_tail {n k : ℕ} (hkpos : 0 < k) (hk9 : k < 9) (hn94 : 94 ≤ n) :
    k ^ k < n ^ (k - Nat.primeCounting k) := by sorry
