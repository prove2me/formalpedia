-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter23_chapter23
-- name    : ProofsInTheBook.Chapter23.chapter23
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T16:10:43.524177+00:00
-- url     : https://prove2.me/theorems/7cce131c-93ff-4234-8670-7216301aa83b
-- title:
--   Littlewood–Offord bound for subset sums
-- statement:
--   Let $n\in\mathbb N$, let $a:\operatorname{Fin}(n)\to\mathbb R$ satisfy $a_i\ge1$ for every $i$, and let $x\in\mathbb R$. For each subset $S$ of the index set, write $s(S)=\sum_{i\in S}a_i$. Then
--   $$\left|\left\{S\subseteq\operatorname{Fin}(n):x\le s(S)<x+1\right\}\right|\le {n\choose\lfloor n/2\rfloor}.$$
--
--   This is the positive-weight subset-sum form of Littlewood–Offord concentration, using a half-open interval. The signed-sum formulation is not part of this statement.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 25, “On a lemma of Littlewood and Offord”, pp. 179–182 (https://doi.org/10.1007/978-3-662-57265-8_25). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter23.lean#L96. The chapter reference identifies the topic; it does not claim the Lean development reproduces every argument of that chapter.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter23
open Finset
open ProofsInTheBook.Chapter23

theorem ProofsInTheBook.Chapter23.chapter23 {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 1 ≤ a i) (x : ℝ) :
    (shortIntervalSubsetSums a x).card ≤ n.choose (n / 2) := by sorry
