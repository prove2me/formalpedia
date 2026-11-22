-- Prove2me | Theorems.Thm_disjointComplement_inter_eq_zero
-- name    : disjointComplement_inter_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:30:30.052994+00:00
-- url     : https://prove2.me/theorems/d8ffd92d-e8a9-459e-986a-c7902e2a9e76
-- title:
--   disjoint Complement inter eq zero: disjoint Complement inter eq zero
-- statement:
--   The intersection of a set with its disjoint complement is contained in
--   `{0}`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Band/DisjointComplement.lean#L53-L58
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Band/DisjointComplement.lean#L53-L58

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Band_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Band_DisjointComplement
set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
omit [VectorLattice X]

theorem disjointComplement_inter_eq_zero (A : Set X) :
    A ∩ Aᵈ ⊆ {0} := by sorry
