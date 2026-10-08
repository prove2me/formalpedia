-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter22_rowLinearCapacityAtLeastOne_of_doublyStochastic
-- name    : ProofsInTheBook.Chapter22.rowLinearCapacityAtLeastOne_of_doublyStochastic
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T17:04:45.023348+00:00
-- url     : https://prove2.me/theorems/45ec936f-ae31-4a27-8916-7a2e945fed63
-- title:
--   Capacity at least one for a doubly stochastic row product
-- statement:
--   Let $n\geq0$ and let $A$ be a real $n\times n$ matrix with nonnegative entries and every row and column sum equal to 1. For every vector $x$ with strictly positive coordinates, $$\prod_{j=1}^n x_j\leq\prod_{i=1}^n\left(\sum_{j=1}^n A_{ij}x_j\right).$$ This is the predicate RowLinearCapacityAtLeastOne; it includes the empty-matrix case.
-- source:
--   Repository declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter22.lean#L295. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 24, “Van der Waerden’s permanent conjecture”, pp. 169–177 (https://doi.org/10.1007/978-3-662-57265-8_24). Auxiliary statements are cited to the repository and are not asserted to be separately numbered book theorems.

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter22
set_option autoImplicit true
open ProofsInTheBook.Chapter22
open Matrix
open ProofsInTheBook.PermanentConvexity

theorem ProofsInTheBook.Chapter22.rowLinearCapacityAtLeastOne_of_doublyStochastic {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    RowLinearCapacityAtLeastOne A := by sorry
