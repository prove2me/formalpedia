-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_induce_union_geodesic_isTree
-- name    : WrittenOnTheWallII.GraphConjecture84.induce_union_geodesic_isTree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:23:33.917083+00:00
-- url     : https://prove2.me/theorems/a7e8251c-63fc-4918-adf5-a75cf56ef585
-- title:
--   Graph Conjecture84: induce union geodesic is Tree
-- statement:
--   A geodesic meeting an induced tree only at its end attaches without creating a cycle
--   when every edge from the new vertices to the tree ends at that common vertex.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L258-L309
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L258-L309

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

theorem WrittenOnTheWallII.GraphConjecture84.induce_union_geodesic_isTree {G : SimpleGraph α} (hG : G.Connected)
    {u v : α} (p : G.Walk u v) (hp : p.length = G.dist u v) (s : Finset α)
    (hs : (G.induce (s : Set α)).IsTree) (hv : v ∈ s)
    (hinter : ∀ z ∈ p.support, z ∈ s → z = v)
    (hcross : ∀ z ∈ p.support, z ≠ v → ∀ w ∈ s, G.Adj z w → w = v) :
    (G.induce ((p.support.toFinset ∪ s : Finset α) : Set α)).IsTree := by sorry
