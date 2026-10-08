-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_chapter03_erdos_ge3
-- name    : ProofsInTheBook.Chapter03.chapter03_erdos_ge3
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T16:26:05.889477+00:00
-- url     : https://prove2.me/theorems/45b2544a-28fb-4a89-a767-f8708c5f1129
-- title:
--   Binomial coefficients are not powers of exponent at least three
-- statement:
--   For all $n,k,\ell,m\in\mathbb N$ satisfying $k\ge4$, $2k\le n$, and $\ell\ge3$,
--   $$\binom nk\ne m^\ell.$$
-- source:
--   Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L5395. This is a selected result in the local development concerning binomial coefficients and their prime factors. The specific technical formulation is cited to the repository, without claiming that it appears verbatim in the textbook.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.chapter03_erdos_ge3
    {n k l m : ℕ} (hk : 4 ≤ k) (hn : 2 * k ≤ n) (hl : 3 ≤ l) :
    n.choose k ≠ m ^ l := by sorry
