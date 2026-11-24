-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_not_connected_induce_delete_of_separated_pair
-- name    : WrittenOnTheWallII.GraphConjecture84.not_connected_induce_delete_of_separated_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:24:59.425675+00:00
-- url     : https://prove2.me/theorems/12cbf287-d41e-4a76-a238-67659b667daf
-- title:
--   Graph Conjecture84: not connected induce delete of separated pair
-- statement:
--   A separated pair in the ambient deletion graph certifies a cut in any induced graph
--   containing that pair and the deleted vertex.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L831-L857
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L831-L857

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

theorem WrittenOnTheWallII.GraphConjecture84.not_connected_induce_delete_of_separated_pair {G : SimpleGraph α}
    {S : Set α} {c a b : α} (hcS : c ∈ S) (haS : a ∈ S) (hbS : b ∈ S)
    (hac : a ≠ c) (hbc : b ≠ c)
    (hsep : ¬ (G.induce ({c}ᶜ : Set α)).Reachable
      ⟨a, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hac⟩
      ⟨b, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hbc⟩) :
    ¬ ((G.induce S).induce ({(⟨c, hcS⟩ : S)}ᶜ : Set S)).Connected := by sorry
