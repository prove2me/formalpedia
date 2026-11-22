-- Prove2me | Theorems.Thm_disjointComplement_union
-- name    : disjointComplement_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:30:41.322075+00:00
-- url     : https://prove2.me/theorems/1731b92d-c26a-424c-b65f-e8f125723fd1
-- title:
--   disjoint Complement union: disjoint Complement union
-- statement:
--   The disjoint complement of a union is the intersection of the disjoint
--   complements.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Band/DisjointComplement.lean#L76-L83
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Band/DisjointComplement.lean#L76-L83

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

theorem disjointComplement_union (A B : Set X) :
    (A ∪ B)ᵈ = Aᵈ ∩ Bᵈ := by sorry
