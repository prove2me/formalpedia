-- Prove2me | Theorems.Thm_abs_sup_of_isVLDisjoint
-- name    : abs_sup_of_isVLDisjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:16:53.884245+00:00
-- url     : https://prove2.me/theorems/b83b4f53-9dad-41e2-99c7-89d9c4a518d3
-- title:
--   abs sup of is VLDisjoint: abs sup of is VLDisjoint
-- statement:
--   Absolute value preserves the supremum of nonnegative elements.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L157-L159
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L157-L159

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

theorem abs_sup_of_isVLDisjoint {x y : X} (hx : 0 ≤ x) (hy : 0 ≤ y)
    : |x ⊔ y| = |x| ⊔ |y| := by sorry
