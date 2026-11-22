-- Prove2me | Theorems.Thm_sup_abs_eq_add_abs_of_isVLDisjoint
-- name    : sup_abs_eq_add_abs_of_isVLDisjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:55.899806+00:00
-- url     : https://prove2.me/theorems/0a238cdc-1252-4c6a-b913-d3e066c60b26
-- title:
--   sup abs eq add abs of is VLDisjoint: sup abs eq add abs of is VLDisjoint
-- statement:
--   If `x ⊥ y` then `|x| ⊔ |y| = |x| + |y|`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L218-L222
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L218-L222

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

theorem sup_abs_eq_add_abs_of_isVLDisjoint {x y : X}
    (h : IsVLDisjoint x y) : |x| ⊔ |y| = |x| + |y| := by sorry
