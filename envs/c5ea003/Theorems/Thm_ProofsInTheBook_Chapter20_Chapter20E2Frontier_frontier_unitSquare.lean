-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter20_Chapter20E2Frontier_frontier_unitSquare
-- name    : ProofsInTheBook.Chapter20.Chapter20E2Frontier.frontier_unitSquare
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T17:46:21.960393+00:00
-- url     : https://prove2.me/theorems/133fd440-dc1f-4881-a7da-f01ba0fba300
-- title:
--   The frontier of the closed unit square
-- statement:
--   In the real plane, $$\partial([0,1]^2)=\{(x,y):0\leq x\leq1,\ 0\leq y\leq1,\ x=0\ \text{or}\ x=1\ \text{or}\ y=0\ \text{or}\ y=1\}.$$ The frontier is taken in the ordinary topology of the plane. There are no dissection or coloring hypotheses.
-- source:
--   Original declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter20E2Frontier.lean#L586. Repository topic: Monsky’s theorem, “One square and an odd number of triangles.”

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter20
set_option autoImplicit true
open ProofsInTheBook.Chapter20
open scoped Topology
open ProofsInTheBook.Chapter20.Chapter20E2Frontier

theorem ProofsInTheBook.Chapter20.Chapter20E2Frontier.frontier_unitSquare :
    frontier (Set.Icc ((0, 0) : P) (1, 1)) =
      {p : P | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 ∧
        (p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1)} := by sorry
