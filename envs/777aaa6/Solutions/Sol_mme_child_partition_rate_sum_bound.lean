-- Prove2me | solution 1 for mme_child_partition_rate_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:59:53.251979+00:00
-- url     : https://prove2.me/submissions/40053b22-13aa-4777-929b-bfb7a9724ee9

import Theorems.Thm_mme_boundary_normalized_weight_rate_bound

open scoped BigOperators

/-- Bounds for the two parts of any finite child partition combine with one
loss per original cell, independently of the enumeration chosen by extraction. -/
theorem solution {C : Type*} [Fintype C]
    (nB nI : ℕ) (e : (Fin nB ⊕ Fin nI) ≃ C)
    (q : C → ℝ) (b : Fin nB → ℝ) (i : Fin nI → ℝ)
    (scale loss : ℝ)
    (hb : ∀ r, scale * (q (e (.inl r)) - loss) ≤ b r)
    (hi : ∀ r, scale * (q (e (.inr r)) - loss) ≤ i r) :
    scale * ((∑ c, q c) - (Fintype.card C : ℝ) * loss) ≤
      (∑ r, b r) + ∑ r, i r := by
  classical
  have hs : (∑ c, scale * (q c - loss)) =
      (∑ r : Fin nB, scale * (q (e (.inl r)) - loss)) +
        ∑ r : Fin nI, scale * (q (e (.inr r)) - loss) := by
    rw [← e.sum_comp]
    exact Fintype.sum_sum_type _
  calc
    scale * ((∑ c, q c) - (Fintype.card C : ℝ) * loss) =
        ∑ c, scale * (q c - loss) := by
      simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    _ = _ := hs
    _ ≤ _ := add_le_add (Finset.sum_le_sum fun r _ ↦ hb r)
      (Finset.sum_le_sum fun r _ ↦ hi r)


#print axioms solution
