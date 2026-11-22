-- Prove2me | Theorems.Thm_subset_disjointComplement_disjointComplement
-- name    : subset_disjointComplement_disjointComplement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:30:37.575797+00:00
-- url     : https://prove2.me/theorems/ecc03045-8f5d-47e9-b036-046bd60a75e9
-- title:
--   subset disjoint Complement disjoint Complement: subset disjoint Complement disjoint Complement
-- statement:
--   Every set is contained in its double disjoint complement.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Band/DisjointComplement.lean#L62-L63
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Band/DisjointComplement.lean#L62-L63

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

theorem subset_disjointComplement_disjointComplement (A : Set X) :
    A ⊆ Aᵈᵈ := by sorry
