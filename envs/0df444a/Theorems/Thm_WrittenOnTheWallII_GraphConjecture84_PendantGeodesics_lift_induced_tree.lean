-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_lift_induced_tree
-- name    : WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.lift_induced_tree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:31:54.361831+00:00
-- url     : https://prove2.me/theorems/ebda19e1-0c88-4354-9b72-993907f4c035
-- title:
--   Pendant Geodesics: lift induced tree
-- statement:
--   Adjoining the pendant paths at the vertices of an induced core tree gives
--   an induced tree whose order is multiplied by the common path order.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1872-L1948
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1872-L1948

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
set_option maxHeartbeats 800000

theorem WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.lift_induced_tree (hG : G.Connected) (L : ℕ)
    (hLen : ∀ c, (F.path c).length = L)
    (s : Finset ↥(K : Set α))
    (hs : ((G.induce (K : Set α)).induce (s : Set ↥(K : Set α))).IsTree) :
    s.card * (L + 1) ≤ largestInducedTreeSize G := by sorry
