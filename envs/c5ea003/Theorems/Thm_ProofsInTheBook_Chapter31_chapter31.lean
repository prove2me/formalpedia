-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter31_chapter31
-- name    : ProofsInTheBook.Chapter31.chapter31
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T16:20:04.601984+00:00
-- url     : https://prove2.me/theorems/e98f7159-97e9-4cdb-84dc-66ce9af61c17
-- title:
--   Cayley’s formula for labeled trees
-- statement:
--   For every natural number $n\ge2$, let $\mathcal T_n$ be the set of simple graphs on $\operatorname{Fin}(n)$ that are trees. Then
--   $$|\mathcal T_n|=n^{n-2}.$$
--
--   The labels are the fixed vertex indices, so isomorphic graphs with different labelings are counted separately. This is the full labeled-tree count for the stated range.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 33, “Cayley’s formula for the number of trees”, pp. 235–240 (https://doi.org/10.1007/978-3-662-57265-8_33). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter31.lean#L2673. The chapter reference identifies the topic; it does not claim the Lean development reproduces every argument of that chapter.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter31

set_option autoImplicit true
open ProofsInTheBook.Chapter31
open SimpleGraph

theorem ProofsInTheBook.Chapter31.chapter31 (n : ℕ) (hn : 2 ≤ n) :
    Fintype.card (LabeledTree n) = n ^ (n - 2) := by sorry
