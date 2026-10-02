-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter10_euclidean_sylvester_gallai
-- name    : ProofsInTheBook.Chapter10.euclidean_sylvester_gallai
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:10:25.339257+00:00
-- url     : https://prove2.me/theorems/0a34fd09-2478-4379-878a-2c98d608a9c3
-- title:
--   The Sylvester–Gallai ordinary line theorem
-- statement:
--   Let $S$ be a finite subset of the real Euclidean plane. Suppose there are $P,u,v\in S$ with $u\ne v$ and P not on the affine line through u and v. Then there are distinct $a,b\in S$ such that
--   $$\bigl|S\cap\operatorname{aff}_{\mathbb R}\{a,b\}\bigr|=2.$$
--   Thus the line through a and b contains exactly those two points of S. The off-line triple is the explicit noncollinearity hypothesis of the formal statement.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 11, “Lines in the plane and decompositions of graphs”, pp. 77–82 (https://doi.org/10.1007/978-3-662-57265-8_11). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter10.lean#L669. The citation identifies the topic, not complete formalization of every result in that chapter.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter10
open Metric
open scoped Classical
open ProofsInTheBook.Chapter10

theorem ProofsInTheBook.Chapter10.euclidean_sylvester_gallai (S : Finset EPoint) (T : OffLineTriple S) :
    ∃ a b : EPoint, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      (S.filter (· ∈ affineSpan ℝ ({a, b} : Set EPoint))).card = 2 := by sorry
