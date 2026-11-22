-- Prove2me | Theorems.Thm_disjointComplement_union_disjointComplement_eq_singleton
-- name    : disjointComplement_union_disjointComplement_eq_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:30:38.188169+00:00
-- url     : https://prove2.me/theorems/374e7ae9-7274-489c-8f66-5ddebaac043e
-- title:
--   disjoint Complement union disjoint Complement eq singleton: disjoint Complement union disjoint Complement eq singleton
-- statement:
--   The disjoint complement of a set together with its disjoint complement is
--   the singleton `{0}`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Band/DisjointComplement.lean#L88-L96
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Band/DisjointComplement.lean#L88-L96

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

theorem disjointComplement_union_disjointComplement_eq_singleton (A : Set X) :
    (A ∪ Aᵈ)ᵈ = ({0} : Set X) := by sorry
