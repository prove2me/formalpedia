-- Prove2me | Theorems.Thm_isMaximalDisjoint_iff_forall_eq_zero
-- name    : isMaximalDisjoint_iff_forall_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:17:16.300797+00:00
-- url     : https://prove2.me/theorems/662f1042-b04c-4921-9334-7de1acf8310b
-- title:
--   is Maximal Disjoint iff forall eq zero: is Maximal Disjoint iff forall eq zero
-- statement:
--   A pairwise disjoint family of nonzero elements is maximal iff
--   the only element disjoint from every member of the family is `0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L498-L538
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L498-L538

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
omit [VectorLattice X]

theorem isMaximalDisjoint_iff_forall_eq_zero {Λ : Set X}
    (hdis : IsDisjointSet Λ) :
    IsMaximalDisjoint Λ ↔ ∀ x : X, (∀ a ∈ Λ, IsVLDisjoint x a) → x = 0 := by sorry
