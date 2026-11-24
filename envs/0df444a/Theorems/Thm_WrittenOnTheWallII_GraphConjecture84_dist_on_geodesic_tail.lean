-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_dist_on_geodesic_tail
-- name    : WrittenOnTheWallII.GraphConjecture84.dist_on_geodesic_tail
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:28:35.835278+00:00
-- url     : https://prove2.me/theorems/9a80fd6e-2936-494e-a6d9-6f99a6f49db3
-- title:
--   Graph Conjecture84: dist on geodesic tail
-- statement:
--   Along the tail of a geodesic, distance from its start is one more than distance
--   from its first neighbor.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L356-L367
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L356-L367

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem WrittenOnTheWallII.GraphConjecture84.dist_on_geodesic_tail {G : SimpleGraph α} (hG : G.Connected)
    {u n v z : α} (hun : G.Adj u n) (p : G.Walk n v)
    (hp : (p.cons hun).length = G.dist u v) (hz : z ∈ p.support) :
    G.dist u z = G.dist n z + 1 := by sorry
