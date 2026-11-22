-- Prove2me | Theorems.Thm_abs_add_eq_sup_abs_of_isVLDisjoint
-- name    : abs_add_eq_sup_abs_of_isVLDisjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:16:55.55594+00:00
-- url     : https://prove2.me/theorems/d1688f96-d045-45f9-a1f0-3ad4e86b9cac
-- title:
--   abs add eq sup abs of is VLDisjoint: abs add eq sup abs of is VLDisjoint
-- statement:
--   If `x ⊥ y` then `|x + y| = |x| ⊔ |y|`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L225-L227
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L225-L227

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

theorem abs_add_eq_sup_abs_of_isVLDisjoint {x y : X}
    (h : IsVLDisjoint x y) : |x + y| = |x| ⊔ |y| := by sorry
