-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_dist_eq_add_of_not_reachable_compl
-- name    : WrittenOnTheWallII.GraphConjecture84.dist_eq_add_of_not_reachable_compl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:23:47.83507+00:00
-- url     : https://prove2.me/theorems/edd4de7c-3f36-4ae4-967e-9029a915190f
-- title:
--   Graph Conjecture84: dist eq add of not reachable compl
-- statement:
--   Vertices in different deletion components have all shortest paths through the cut vertex.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L692-L705
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L692-L705

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

theorem WrittenOnTheWallII.GraphConjecture84.dist_eq_add_of_not_reachable_compl {G : SimpleGraph α} (hG : G.Connected)
    {c a b : α} (ha : a ≠ c) (hb : b ≠ c)
    (hsep : ¬ (G.induce ({c}ᶜ : Set α)).Reachable
      ⟨a, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ha⟩
      ⟨b, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hb⟩) :
    G.dist a b = G.dist a c + G.dist c b := by sorry
