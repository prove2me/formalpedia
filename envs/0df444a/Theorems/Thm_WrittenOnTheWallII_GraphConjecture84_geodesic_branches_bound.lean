-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_geodesic_branches_bound
-- name    : WrittenOnTheWallII.GraphConjecture84.geodesic_branches_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:29:08.137238+00:00
-- url     : https://prove2.me/theorems/668643bc-7d76-4b91-956b-d9a05a5d5b76
-- title:
--   Graph Conjecture84: geodesic branches bound
-- statement:
--   The supports of two geodesics in separate branches induce a tree of their combined order.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L605-L642
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L605-L642

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

theorem WrittenOnTheWallII.GraphConjecture84.geodesic_branches_bound {G : SimpleGraph α} (hG : G.Connected)
    {c a b : α} (p : G.Walk c a) (q : G.Walk c b)
    (hp : p.length = G.dist c a) (hq : q.length = G.dist c b)
    (hinter : ∀ z ∈ p.support, z ∈ q.support → z = c)
    (hsep : ∀ z ∈ p.support, z ≠ c → ∀ y ∈ q.support, y ≠ c → ¬ G.Adj z y) :
    p.length + q.length + 1 ≤ largestInducedTreeSize G := by sorry
