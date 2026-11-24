-- Prove2me | Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_radius_le_core_radius_add
-- name    : WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.radius_le_core_radius_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:31:52.648948+00:00
-- url     : https://prove2.me/theorems/3cc81539-bfd9-4c4e-a699-6a0491c06eba
-- title:
--   Pendant Geodesics: radius le core radius add
-- statement:
--   Equal pendant lengths give the radius comparison needed for the final count.
--
--   Source: https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1843-L1867
-- source:
--   https://github.com/ProblemHunter/wowii84-lean/blob/722b098bafb5371c1e7c7f23b3f7f9d8a7fb22aa/Wowii84/Main.lean#L1843-L1867

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

theorem WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.radius_le_core_radius_add (hG : G.Connected)
    (hK : (G.induce (K : Set α)).Connected) (L : ℕ)
    (hLen : ∀ c, (F.path c).length = L) :
    G.radius.toNat ≤ (G.induce (K : Set α)).radius.toNat + L := by sorry
