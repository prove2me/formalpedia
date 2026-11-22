-- Prove2me | Theorems.Thm_isVLDisjoint_sub_inf
-- name    : isVLDisjoint_sub_inf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:17:07.340804+00:00
-- url     : https://prove2.me/theorems/2d8d328e-76e5-4924-aa58-7f04d284090e
-- title:
--   is VLDisjoint sub inf: is VLDisjoint sub inf
-- statement:
--   For any `x, y`, the elements `x - x ⊓ y` and `y - x ⊓ y` are non-negative
--   and disjoint.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L278-L284
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L278-L284

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

theorem isVLDisjoint_sub_inf (x y : X) :
    IsVLDisjoint (x - x ⊓ y) (y - x ⊓ y) := by sorry
