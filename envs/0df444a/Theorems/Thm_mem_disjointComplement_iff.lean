-- Prove2me | Theorems.Thm_mem_disjointComplement_iff
-- name    : mem_disjointComplement_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:30:50.843069+00:00
-- url     : https://prove2.me/theorems/4efc80e4-76ed-47eb-b6f9-c103493f1375
-- title:
--   mem disjoint Complement iff: mem disjoint Complement iff
-- statement:
--   Membership in the disjoint complement: `x ∈ Aᵈ` iff `x` is disjoint from
--   every member of `A`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Band/DisjointComplement.lean#L42-L43
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Band/DisjointComplement.lean#L42-L43

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Band_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Band_DisjointComplement
set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
omit [IsOrderedAddMonoid X] [VectorLattice X]

theorem mem_disjointComplement_iff {A : Set X} {x : X} :
    x ∈ Aᵈ ↔ ∀ a ∈ A, IsVLDisjoint x a := by sorry
