-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter14_chapter14_unconditional
-- name    : ProofsInTheBook.Chapter14.chapter14_unconditional
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:08:51.295337+00:00
-- url     : https://prove2.me/theorems/133c5c6c-b8a7-45c4-b004-f40acc0b9328
-- title:
--   A bound for simplices touching along facet interiors
-- statement:
--   Let $d\in\mathbb N$ with $d>0$, let I be a finite index set, and let $(S_i)_{i\in I}$ be a family of d-dimensional simplices in $\mathbb R^d$. Each simplex has d+1 affinely independent vertices. Suppose that, for every pair of distinct indices i,j, the relative interiors of $S_i$ and $S_j$ are disjoint, and there are facets $F_i$ of $S_i$ and $F_j$ of $S_j$ satisfying
--   $$\operatorname{aff}(F_i)=\operatorname{aff}(F_j),\qquad \operatorname{relint}(F_i)\cap\operatorname{relint}(F_j)\ne\varnothing.$$
--   Here a facet is the simplex spanned by all vertices except one, and its relative interior is taken in its own affine hyperplane. Then
--   $$|I|<2^{d+1}.$$
--   The family may be empty. This statement uses overlap of facet relative interiors, not merely contact at a vertex or another lower-dimensional boundary set. No separate facet-separation certificate is assumed.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 16, “Touching simplices”, pp. 107–110 (https://doi.org/10.1007/978-3-662-57265-8_16). Precise formal statement: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter14.lean#L2824. The book reference identifies the topic; the displayed contact convention and bound are those of the cited formalization.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter14
open ProofsInTheBook.Chapter14
open scoped Classical Topology
set_option synthInstance.maxHeartbeats 80000

theorem ProofsInTheBook.Chapter14.chapter14_unconditional {ι : Type*} [Fintype ι]
    {d : ℕ} [NeZero d] (simplices : ι → DSimplex d)
    (htouch : FaithfulPairwiseTouching simplices) :
    Fintype.card ι < 2 ^ (d + 1) := by sorry
