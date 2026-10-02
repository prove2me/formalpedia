-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter34_chapter34
-- name    : ProofsInTheBook.Chapter34.chapter34
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:11:42.778993+00:00
-- url     : https://prove2.me/theorems/bf27ff00-4fea-40e6-b1c4-7d64834196b4
-- title:
--   Dinitz’s list-coloring theorem
-- statement:
--   Let $n\in\mathbb N$ and let $\alpha$ be a color type with decidable equality. For every cell $(i,j)\in\operatorname{Fin}(n)^2$, let $L_{ij}$ be a finite subset of $\alpha$ with $|L_{ij}|\ge n$. There exists a coloring $c:\operatorname{Fin}(n)^2\to\alpha$ such that
--   $$c(i,j)\in L_{ij},\qquad j\ne j'\Rightarrow c(i,j)\ne c(i,j'),\qquad i\ne i'\Rightarrow c(i,j)\ne c(i',j).$$
--   The inequalities range over all appropriate row and column indices.
--
--   This is the list-coloring assertion of the Dinitz problem, including the empty array.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 38, “The Dinitz problem”, pp. 271–276 (https://doi.org/10.1007/978-3-662-57265-8_38). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter34.lean#L677. The chapter reference identifies the topic; it does not claim the Lean development reproduces every argument of that chapter.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter34
open ProofsInTheBook.Chapter34

theorem ProofsInTheBook.Chapter34.chapter34 {n : ℕ} {α : Type*} [DecidableEq α]
    (lists : Cell n → Finset α)
    (hlists : ∀ cell, n ≤ (lists cell).card) :
    ∃ color : Cell n → α, DinitzSolution lists color := by sorry
