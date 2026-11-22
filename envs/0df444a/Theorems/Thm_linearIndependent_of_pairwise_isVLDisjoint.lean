-- Prove2me | Theorems.Thm_linearIndependent_of_pairwise_isVLDisjoint
-- name    : linearIndependent_of_pairwise_isVLDisjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:17:16.995726+00:00
-- url     : https://prove2.me/theorems/e5d009c0-94fa-4733-a477-278f41b90db4
-- title:
--   linear Independent of pairwise is VLDisjoint: linear Independent of pairwise is VLDisjoint
-- statement:
--   A pairwise-disjoint family of non-zero vectors is linearly independent
--   over `ℝ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L456-L474
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L456-L474

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

theorem linearIndependent_of_pairwise_isVLDisjoint {n : ℕ} {x : Fin n → X}
    (hne : ∀ i, x i ≠ 0)
    (hdisj : Pairwise fun i j => IsVLDisjoint (x i) (x j)) :
    LinearIndependent ℝ x := by sorry
