-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter27_chapter27
-- name    : ProofsInTheBook.Chapter27.chapter27
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T16:11:32.816042+00:00
-- url     : https://prove2.me/theorems/fe0ea2f9-6139-4ffe-b4cf-0c9b82ef88dd
-- title:
--   De Bruijn’s rectangle tiling criterion
-- statement:
--   Let $n,a,b\in\mathbb N$ with $n\ge2$. Define a tiling of the grid $\operatorname{Fin}(a)\times\operatorname{Fin}(b)$ to be a finite disjoint cover by horizontal runs of $n$ consecutive cells or vertical runs of $n$ consecutive cells, each lying in the grid. Then
--   $$\operatorname{IsTiledByNxOne}(n,a,b)\quad\Longleftrightarrow\quad n\mid a\ \lor\ n\mid b.$$
--
--   The statement concerns axis-aligned integer-grid bricks and permits zero side lengths. It combines the divisibility obstruction with the explicit stripe tilings.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 29, “Tiling rectangles”, pp. 207–211 (https://doi.org/10.1007/978-3-662-57265-8_29). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter27.lean#L375. The chapter reference identifies the topic; it does not claim the Lean development reproduces every argument of that chapter.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter27
open Complex Finset Real IsPrimitiveRoot
open ProofsInTheBook.Chapter27

theorem ProofsInTheBook.Chapter27.chapter27 (n a b : ℕ) (hn : 2 ≤ n) :
    IsTiledByNxOne n a b ↔ n ∣ a ∨ n ∣ b := by sorry
