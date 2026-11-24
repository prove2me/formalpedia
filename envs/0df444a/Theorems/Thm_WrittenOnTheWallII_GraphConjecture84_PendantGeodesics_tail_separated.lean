-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_tail_separated
-- name    : WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.tail_separated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:24:07.550789+00:00
-- url     : https://prove2.me/theorems/69931b06-e8ba-4eb3-87fb-504814e4b2b3
-- title:
--   Pendant Geodesics: tail separated
-- statement:
--   Deleting a pendant root separates its positive tail from everything off its path.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1540-L1551
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1540-L1551

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
open WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
variable {G : SimpleGraph α} {K : Finset α} (F : PendantGeodesics G K)

theorem WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.tail_separated (c : ↥(K : Set α)) {z v : α}
    (hz : z ∈ (F.path c).support) (hzc : z ≠ (c : α))
    (hv : v ∉ (F.path c).support) :
    ¬ (G.induce ({(c : α)}ᶜ : Set α)).Reachable
      ⟨z, by simpa using hzc⟩
      ⟨v, by simpa using (show v ≠ (c : α) from fun heq => hv (heq ▸ (F.path c).start_mem_support))⟩ := by sorry
