-- Prove2me | Theorems.Thm_abs_sum_finset
-- name    : abs_sum_finset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:13:59.030882+00:00
-- url     : https://prove2.me/theorems/4ccf87fe-91a7-48fa-9374-ac98311f8960
-- title:
--   abs sum finset: abs sum finset
-- statement:
--   Absolute value distributes over a scaled finite disjoint family.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L414-L431
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L414-L431

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

theorem abs_sum_finset {ι : Type*} (s : Finset ι) (x : ι → X) (α : ι → ℝ)
    (hdisj : (s : Set ι).Pairwise fun i j => IsVLDisjoint (x i) (x j)) :
    |∑ i ∈ s, α i • x i| = ∑ i ∈ s, |α i| • |x i| := by sorry
