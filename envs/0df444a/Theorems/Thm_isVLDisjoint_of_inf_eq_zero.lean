-- Prove2me | Theorems.Thm_isVLDisjoint_of_inf_eq_zero
-- name    : isVLDisjoint_of_inf_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:28.63751+00:00
-- url     : https://prove2.me/theorems/1e2b8ac3-c328-46b6-8196-9ada8a5ae09e
-- title:
--   is VLDisjoint of inf eq zero: is VLDisjoint of inf eq zero
-- statement:
--   If `x ⊓ y = 0` then `x` and `y` are disjoint.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L61-L65
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L61-L65

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

theorem isVLDisjoint_of_inf_eq_zero {x y : X}
    (h : x ⊓ y = 0) : IsVLDisjoint x y := by sorry
