-- Prove2me | Theorems.Thm_exists_isMaximalDisjoint_pos
-- name    : exists_isMaximalDisjoint_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:17:18.646299+00:00
-- url     : https://prove2.me/theorems/80db1194-e0b0-4643-8ca7-811f8b808b69
-- title:
--   exists is Maximal Disjoint pos: exists is Maximal Disjoint pos
-- statement:
--   **Existence of a maximal disjoint family of positive vectors.** Every
--   vector lattice admits a maximal disjoint family whose elements are all
--   strictly positive.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L543-L597
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L543-L597

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

theorem exists_isMaximalDisjoint_pos (X : Type*) [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] :
    ∃ Λ : Set X, IsMaximalDisjoint Λ ∧ ∀ x ∈ Λ, 0 < x := by sorry
