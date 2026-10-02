-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter20_mem_segment_unit_left
-- name    : ProofsInTheBook.Chapter20.mem_segment_unit_left
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T17:46:30.563929+00:00
-- url     : https://prove2.me/theorems/035cc0dd-cff5-4de1-9d07-e7ff7fa3b81f
-- title:
--   Coordinate description of the unit square’s left segment
-- statement:
--   For every $p=(x,y)\in\mathbb R^2$, $$p\in[(0,1),(0,0)]\quad\Longleftrightarrow\quad x=0\ \text{and}\ 0\leq y\leq1.$$ The segment is closed. There are no dissection hypotheses.
-- source:
--   Original declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter20E2Boundary.lean#L1134. Repository topic: Monsky’s theorem, “One square and an odd number of triangles.”

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter20
set_option autoImplicit true
open ProofsInTheBook.Chapter20
open MonskyColor
variable (D : SquareDissection)

lemma ProofsInTheBook.Chapter20.mem_segment_unit_left (p : ℝ × ℝ) :
    p ∈ segment ℝ ((0, 1) : ℝ × ℝ) (0, 0) ↔
      p.1 = 0 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 := by sorry
