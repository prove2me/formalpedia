-- Prove2me | Theorems.Thm_isVLDisjoint_zero_left
-- name    : isVLDisjoint_zero_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:34.11783+00:00
-- url     : https://prove2.me/theorems/30959cbe-7ae1-4b84-9a17-6bd3c63ee6c9
-- title:
--   is VLDisjoint zero left: is VLDisjoint zero left
-- statement:
--   Zero is disjoint from every element.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L48-L49
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L48-L49

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

theorem isVLDisjoint_zero_left (x : X) : IsVLDisjoint 0 x := by sorry
