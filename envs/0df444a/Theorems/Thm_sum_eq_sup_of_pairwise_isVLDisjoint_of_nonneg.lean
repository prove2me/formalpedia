-- Prove2me | Theorems.Thm_sum_eq_sup_of_pairwise_isVLDisjoint_of_nonneg
-- name    : sum_eq_sup_of_pairwise_isVLDisjoint_of_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:15:10.531246+00:00
-- url     : https://prove2.me/theorems/5660390a-c7a0-4c92-b8b9-053e4899b70b
-- title:
--   sum eq sup of pairwise is VLDisjoint of nonneg: sum eq sup of pairwise is VLDisjoint of nonneg
-- statement:
--   For a pairwise-disjoint family of non-negative elements, the finite sum
--   equals the supremum.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L326-L333
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/Disjoint.lean#L326-L333

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]

theorem sum_eq_sup_of_pairwise_isVLDisjoint_of_nonneg {n : ℕ} {f : Fin n → X}
    (hne : 0 < n) (hnn : ∀ i, 0 ≤ f i)
    (hdisj : Pairwise fun i j => IsVLDisjoint (f i) (f j)) :
    ∑ i, f i = Finset.univ.sup' (Finset.univ_nonempty_iff.mpr
      ⟨⟨0, hne⟩⟩) f := by sorry
