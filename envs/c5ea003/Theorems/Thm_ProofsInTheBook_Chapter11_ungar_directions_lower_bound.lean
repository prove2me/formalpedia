-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter11_ungar_directions_lower_bound
-- name    : ProofsInTheBook.Chapter11.ungar_directions_lower_bound
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:11:13.518689+00:00
-- url     : https://prove2.me/theorems/097f1f04-a478-46e3-9477-08d9f2ac3c69
-- title:
--   Ungar’s bound on directions determined by planar points
-- statement:
--   Let $S\subseteq\mathbb R^2$ be finite with $n=|S|\ge3$, and suppose S contains three noncollinear points. Let D(S) be the set of directions of lines through distinct pairs of points of S, with a direction specified by its real slope or by the vertical direction. Then
--   $$|D(S)|\ge2\left\lfloor\frac n2\right\rfloor.$$
--   Parallel lines give the same direction, opposite orientations give the same direction, and the vertical direction is included.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 12, “The slope problem”, pp. 83–87 (https://doi.org/10.1007/978-3-662-57265-8_12). Formalization: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter11.lean#L10963. The citation identifies the topic, not complete formalization of every result in that chapter.

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter11
open ProofsInTheBook.Chapter11

theorem ProofsInTheBook.Chapter11.ungar_directions_lower_bound (points : Finset Point2)
    (hn : 3 ≤ points.card)
    (hncoll : NoncollinearSet points) :
    2 * (points.card / 2) ≤ (directionsDeterminedBy points).card := by sorry
