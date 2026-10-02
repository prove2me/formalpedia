-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_chapter03_erdos
-- name    : ProofsInTheBook.Chapter03.chapter03_erdos
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:25:42.748782+00:00
-- url     : https://prove2.me/theorems/72a264be-2e67-415b-a874-86e96147066f
-- title:
--   Binomial coefficients are not perfect powers
-- statement:
--   For all $n,k,\ell,m\in\mathbb N$ satisfying $k\ge4$, $2k\le n$, and $\ell\ge2$,
--   $$\binom nk\ne m^\ell.$$
--   The base m is an arbitrary natural number.
-- source:
--   Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L5628. This is a chapter headline concerning binomial coefficients and their prime factors. Topic reference: Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 3, “Binomial coefficients are (almost) never powers”, pp. 15–18 (https://doi.org/10.1007/978-3-662-57265-8_3).

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.chapter03_erdos {n k l m : ℕ} (hk : 4 ≤ k) (hn : 2 * k ≤ n) (hl : 2 ≤ l) :
    n.choose k ≠ m ^ l := by sorry
