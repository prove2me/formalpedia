-- Prove2me | Theorems.Thm_abs_sum_of_pairwise_isVLDisjoint
-- name    : abs_sum_of_pairwise_isVLDisjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:15:13.993748+00:00
-- url     : https://prove2.me/theorems/3e429259-9bfd-476e-b87a-a56a4fc689b9
-- title:
--   abs sum of pairwise is VLDisjoint: abs sum of pairwise is VLDisjoint
-- statement:
--   For a pairwise-disjoint family and arbitrary scalars,
--   `|∑ i, α i • x i| = ∑ i, |α i| • |x i|`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L435-L438
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L435-L438

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

theorem abs_sum_of_pairwise_isVLDisjoint {n : ℕ} {x : Fin n → X} {α : Fin n → ℝ}
    (hdisj : Pairwise fun i j => IsVLDisjoint (x i) (x j)) :
    |∑ i, α i • x i| = ∑ i, |α i| • |x i| := by sorry
