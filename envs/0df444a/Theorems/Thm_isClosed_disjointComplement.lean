-- Prove2me | Theorems.Thm_isClosed_disjointComplement
-- name    : isClosed_disjointComplement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:30:59.857629+00:00
-- url     : https://prove2.me/theorems/98e8ed8e-e95e-4e75-ba1a-30820c34bb20
-- title:
--   is Closed disjoint Complement: is Closed disjoint Complement
-- statement:
--   In a normed vector lattice, the disjoint complement of any set is norm
--   closed: it is the intersection of the zero-sets of the continuous maps
--   `x ↦ |x| ⊓ |a|`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Band/DisjointComplement.lean#L141-L148
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Band/DisjointComplement.lean#L141-L148

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Band_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Band_DisjointComplement
set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X]

theorem isClosed_disjointComplement (A : Set X) : IsClosed (Aᵈ) := by sorry
