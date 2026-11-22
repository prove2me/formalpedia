-- Prove2me | Theorems.Thm_exists_pair_ne_zero_isVLDisjoint
-- name    : exists_pair_ne_zero_isVLDisjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:15:16.288811+00:00
-- url     : https://prove2.me/theorems/8c08764b-1abd-4d9a-8053-8a9a8b3914fb
-- title:
--   exists pair ne zero is VLDisjoint: exists pair ne zero is VLDisjoint
-- statement:
--   Two non-zero disjoint vectors exist in any Archimedean vector lattice of
--   `ℝ`-rank greater than one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L389-L395
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L389-L395

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

theorem exists_pair_ne_zero_isVLDisjoint [IsVLArchimedean X]
    (h : 1 < Module.rank ℝ X) :
    ∃ u v : X, u ≠ 0 ∧ v ≠ 0 ∧ IsVLDisjoint u v := by sorry
