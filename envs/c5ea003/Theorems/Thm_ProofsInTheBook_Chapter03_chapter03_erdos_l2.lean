-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter03_chapter03_erdos_l2
-- name    : ProofsInTheBook.Chapter03.chapter03_erdos_l2
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T16:25:57.508883+00:00
-- url     : https://prove2.me/theorems/91121f65-22c5-42aa-b7fd-29681e19e82b
-- title:
--   Binomial coefficients are not squares
-- statement:
--   For all $n,k,m\in\mathbb N$ satisfying $k\ge4$ and $2k\le n$,
--   $$\binom nk\ne m^2.$$
-- source:
--   Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L5350. This is a selected result in the local development concerning binomial coefficients and their prime factors. The specific technical formulation is cited to the repository, without claiming that it appears verbatim in the textbook.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter03
open Nat
open ProofsInTheBook.Chapter03

theorem ProofsInTheBook.Chapter03.chapter03_erdos_l2
    {n k m : ℕ} (hk : 4 ≤ k) (hn : 2 * k ≤ n) :
    n.choose k ≠ m ^ 2 := by sorry
