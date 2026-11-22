-- Prove2me | Theorems.Thm_disjointComplement_anti
-- name    : disjointComplement_anti
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:30:33.51896+00:00
-- url     : https://prove2.me/theorems/9bf35d7a-46c7-4869-b509-5ea7cb44fdd2
-- title:
--   disjoint Complement anti: disjoint Complement anti
-- statement:
--   Disjoint complementation is anti-monotone: `A ⊆ B` implies `Bᵈ ⊆ Aᵈ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Band/DisjointComplement.lean#L47-L48
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Substructures/Band/DisjointComplement.lean#L47-L48

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

theorem disjointComplement_anti {A B : Set X} (h : A ⊆ B) :
    Bᵈ ⊆ Aᵈ := by sorry
