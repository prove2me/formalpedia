-- Prove2me | Theorems.Thm_sup_smul_eq_sum_of_pairwise_isVLDisjoint_of_nonneg
-- name    : sup_smul_eq_sum_of_pairwise_isVLDisjoint_of_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:17:20.48138+00:00
-- url     : https://prove2.me/theorems/d1737404-fc65-418c-9b4c-45b89449bc7b
-- title:
--   sup smul eq sum of pairwise is VLDisjoint of nonneg: sup smul eq sum of pairwise is VLDisjoint of nonneg
-- statement:
--   For a pairwise-disjoint family of non-negative elements and non-negative
--   scalars, `∑ i, α i • x i = ⨆ i, α i • x i` (with the sup taken over a
--   non-empty index).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L443-L452
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L443-L452

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

theorem sup_smul_eq_sum_of_pairwise_isVLDisjoint_of_nonneg {n : ℕ}
    {x : Fin n → X} {α : Fin n → ℝ} (hne : 0 < n)
    (hnn : ∀ i, 0 ≤ x i) (hα : ∀ i, 0 ≤ α i)
    (hdisj : Pairwise fun i j => IsVLDisjoint (x i) (x j)) :
    ∑ i, α i • x i = Finset.univ.sup' (Finset.univ_nonempty_iff.mpr
      ⟨⟨0, hne⟩⟩) (fun i => α i • x i) := by sorry
