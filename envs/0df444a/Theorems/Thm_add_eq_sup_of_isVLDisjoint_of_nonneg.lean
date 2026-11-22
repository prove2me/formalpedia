-- Prove2me | Theorems.Thm_add_eq_sup_of_isVLDisjoint_of_nonneg
-- name    : add_eq_sup_of_isVLDisjoint_of_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:53.126804+00:00
-- url     : https://prove2.me/theorems/8f60501c-9311-49ba-bbfa-4385baa3fb8d
-- title:
--   add eq sup of is VLDisjoint of nonneg: add eq sup of is VLDisjoint of nonneg
-- statement:
--   For non-negative disjoint elements, `x + y = x ⊔ y`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L180-L185
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L180-L185

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

theorem add_eq_sup_of_isVLDisjoint_of_nonneg {x y : X}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (h : IsVLDisjoint x y) : x + y = x ⊔ y := by sorry
