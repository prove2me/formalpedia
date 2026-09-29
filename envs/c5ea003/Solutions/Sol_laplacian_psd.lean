-- Prove2me | solution 1 for laplacian_psd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:15:19.304319+00:00
-- url     : https://prove2.me/submissions/e3c327a3-14b0-4b1d-8187-58de12805379

-- Sol generated from Bridges/HilbertPolyaOperator.lean
import Mathlib
import Definitions.Def_Bridges_HilbertPolyaOperator

/-! # CatalogBuild.Bridges.HilbertPolyaOperator

Auto-generated from theorem catalog database.
Domain: Bridges
Declarations: 15
-/

noncomputable section

















theorem solution{n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA_symm : A.IsSymm)
    (hA_nonneg : ∀ i j, A i j ≥ 0)
    (D : Matrix (Fin n) (Fin n) ℝ)
    (hD : ∀ i, D i i = ∑ j, A i j)
    (hD_diag : ∀ i j, i ≠ j → D i j = 0) :
    ∀ v : Fin n → ℝ, v ⬝ᵥ ((D - A).mulVec v) ≥ 0 := by
  intro v
  have h_sum : v ⬝ᵥ (D - A).mulVec v = (1 / 2) * ∑ i, ∑ j, A i j * (v i - v j) ^ 2 := by
    have h_sum : v ⬝ᵥ (D - A).mulVec v = ∑ i, ∑ j, A i j * v i * (v i - v j) := by
      simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_sub, sub_mul, mul_comm, mul_left_comm, Finset.sum_mul, hD, hD_diag ];
      rw [ Finset.sum_congr rfl ];
      intro i hi; rw [ Finset.sum_congr rfl fun j hj => by rw [ show D i j = if i = j then ∑ k, A i k else 0 by aesop ] ] ; simp +decide [ Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, Finset.sum_mul ] ;
    have h_sum_symm : ∑ i, ∑ j, A i j * v i * (v i - v j) = ∑ i, ∑ j, A j i * v j * (v j - v i) := by
      rw [ Finset.sum_comm ];
    have h_sum_symm : ∑ i, ∑ j, A i j * v i * (v i - v j) + ∑ i, ∑ j, A j i * v j * (v j - v i) = ∑ i, ∑ j, A i j * (v i - v j) ^ 2 := by
      rw [ ← Finset.sum_add_distrib ] ; refine' Finset.sum_congr rfl fun i hi => _ ; rw [ ← Finset.sum_add_distrib ] ; refine' Finset.sum_congr rfl fun j hj => _ ; rw [ ← hA_symm.apply ] ; ring;
    linarith;
  exact h_sum.symm ▸ mul_nonneg ( by norm_num ) ( Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => mul_nonneg ( hA_nonneg i j ) ( sq_nonneg _ ) )
