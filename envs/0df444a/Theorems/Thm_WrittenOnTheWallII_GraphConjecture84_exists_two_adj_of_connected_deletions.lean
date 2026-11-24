-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_exists_two_adj_of_connected_deletions
-- name    : WrittenOnTheWallII.GraphConjecture84.exists_two_adj_of_connected_deletions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:23:31.284418+00:00
-- url     : https://prove2.me/theorems/5e09ef3b-bd59-4d4f-a764-4a68b788d656
-- title:
--   Graph Conjecture84: exists two adj of connected deletions
-- statement:
--   A connected graph of order at least three with connected vertex deletions has
--   two distinct neighbors at every vertex.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1283-L1310
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1283-L1310

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

theorem WrittenOnTheWallII.GraphConjecture84.exists_two_adj_of_connected_deletions {G : SimpleGraph α}
    (hcard : 3 ≤ Fintype.card α) (hG : G.Connected)
    (hdel : ∀ x, (G.induce ({x}ᶜ : Set α)).Connected) (c : α) :
    ∃ u v : α, G.Adj c u ∧ G.Adj c v ∧ u ≠ v := by sorry
