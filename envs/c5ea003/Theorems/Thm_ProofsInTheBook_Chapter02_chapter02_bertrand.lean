-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter02_chapter02_bertrand
-- name    : ProofsInTheBook.Chapter02.chapter02_bertrand
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:31:46.979693+00:00
-- url     : https://prove2.me/theorems/e154d7ed-02f7-4ae6-9b9d-1d6e3dcc9807
-- title:
--   Bertrand’s postulate
-- statement:
--   For every natural number $n\ne0$, there exists a prime natural number $p$ such that
--   $$n<p\le2n.$$
--   The upper endpoint is included, so the case $n=1$ is witnessed by $p=2$.
--
--   This is a prime-existence theorem, with no extra prime-gap certificate assumed.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 2, “Bertrand’s postulate”, pp. 9–14 (https://doi.org/10.1007/978-3-662-57265-8_2). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter02.lean#L133. The book citation identifies the topic; the selected declaration has only the scope stated above.

import Mathlib
open Nat Finset

theorem ProofsInTheBook.Chapter02.chapter02_bertrand (n : ℕ) (hn : n ≠ 0) :
    ∃ p, Prime p ∧ n < p ∧ p ≤ 2 * n := by sorry
