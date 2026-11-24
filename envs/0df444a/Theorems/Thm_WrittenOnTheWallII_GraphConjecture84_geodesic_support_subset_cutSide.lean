-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_geodesic_support_subset_cutSide
-- name    : WrittenOnTheWallII.GraphConjecture84.geodesic_support_subset_cutSide
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:24:33.661801+00:00
-- url     : https://prove2.me/theorems/80f05b06-ced9-4d2f-b906-5855f45a1359
-- title:
--   Graph Conjecture84: geodesic support subset cut Side
-- statement:
--   A geodesic from a cut vertex to a point of one side stays in that side.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L713-L728
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L713-L728

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

theorem WrittenOnTheWallII.GraphConjecture84.geodesic_support_subset_cutSide {G : SimpleGraph α} (hG : G.Connected)
    {c v : α} (a : ↥({c}ᶜ : Set α)) (hv : v ∈ cutSide G c a)
    (p : G.Walk c v) (hp : p.length = G.dist c v) :
    ∀ z ∈ p.support, z ∈ cutSide G c a := by sorry
