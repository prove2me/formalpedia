-- Prove2me | Theorems.Thm_nonneg_and_nonneg_of_isVLDisjoint_add_eq_of_nonneg
-- name    : nonneg_and_nonneg_of_isVLDisjoint_add_eq_of_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:16:56.229977+00:00
-- url     : https://prove2.me/theorems/218695d2-c451-4db7-9df8-243042586c50
-- title:
--   nonneg and nonneg of is VLDisjoint add eq of nonneg: nonneg and nonneg of is VLDisjoint add eq of nonneg
-- statement:
--   If a non-negative element is written as a sum of two disjoint elements,
--   then both summands are non-negative.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L189-L215
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L189-L215

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

theorem nonneg_and_nonneg_of_isVLDisjoint_add_eq_of_nonneg
    {x y z : X} (hx : 0 ≤ x) (hyz : IsVLDisjoint y z) (hadd : y + z = x) :
    0 ≤ y ∧ 0 ≤ z := by sorry
