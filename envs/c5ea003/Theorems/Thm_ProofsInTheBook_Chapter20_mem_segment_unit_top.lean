-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter20_mem_segment_unit_top
-- name    : ProofsInTheBook.Chapter20.mem_segment_unit_top
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T17:46:42.271862+00:00
-- url     : https://prove2.me/theorems/6753d43a-8a29-40b2-8ad6-e5f73bb8e87c
-- title:
--   Coordinate description of the unit square’s top segment
-- statement:
--   For every $p=(x,y)\in\mathbb R^2$, $$p\in[(1,1),(0,1)]\quad\Longleftrightarrow\quad 0\leq x\leq1\ \text{and}\ y=1.$$ The segment is closed. There are no dissection hypotheses.
-- source:
--   Original declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter20E2Boundary.lean#L1115. Repository topic: Monsky’s theorem, “One square and an odd number of triangles.”

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter20
set_option autoImplicit true
open ProofsInTheBook.Chapter20
open MonskyColor
variable (D : SquareDissection)

lemma ProofsInTheBook.Chapter20.mem_segment_unit_top (p : ℝ × ℝ) :
    p ∈ segment ℝ ((1, 1) : ℝ × ℝ) (0, 1) ↔
      0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 = 1 := by sorry
