-- Prove2me | Theorems.Thm_isVLDisjoint_posPart_negPart
-- name    : isVLDisjoint_posPart_negPart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:38.096814+00:00
-- url     : https://prove2.me/theorems/14d84355-0b44-469e-9130-e7acb2486976
-- title:
--   is VLDisjoint pos Part neg Part: is VLDisjoint pos Part neg Part
-- statement:
--   The positive and negative parts of an element are disjoint.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L162-L163
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L162-L163

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

theorem isVLDisjoint_posPart_negPart (x : X) : IsVLDisjoint x⁺ x⁻ := by sorry
