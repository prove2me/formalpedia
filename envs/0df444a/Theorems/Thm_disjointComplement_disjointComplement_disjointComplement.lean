-- Prove2me | Theorems.Thm_disjointComplement_disjointComplement_disjointComplement
-- name    : disjointComplement_disjointComplement_disjointComplement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:30:34.815322+00:00
-- url     : https://prove2.me/theorems/fdd4e62a-77ab-43bc-b2c9-ad4350ac047f
-- title:
--   disjoint Complement disjoint Complement disjoint Complement: disjoint Complement disjoint Complement disjoint Complement
-- statement:
--   The triple disjoint complement equals the single disjoint complement.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Band/DisjointComplement.lean#L67-L71
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Band/DisjointComplement.lean#L67-L71

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

theorem disjointComplement_disjointComplement_disjointComplement (A : Set X) :
    Aᵈᵈᵈ = Aᵈ := by sorry
