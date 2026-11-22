-- Prove2me | Theorems.Thm_isVLDisjoint_zero_right
-- name    : isVLDisjoint_zero_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:44.699128+00:00
-- url     : https://prove2.me/theorems/3c56824a-4421-424a-a098-0df00d3e057a
-- title:
--   is VLDisjoint zero right: is VLDisjoint zero right
-- statement:
--   Every element is disjoint from zero.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L52-L53
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L52-L53

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

theorem isVLDisjoint_zero_right (x : X) : IsVLDisjoint x 0 := by sorry
