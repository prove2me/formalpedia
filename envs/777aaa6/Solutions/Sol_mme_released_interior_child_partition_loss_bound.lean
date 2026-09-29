-- Prove2me | solution 1 for mme_released_interior_child_partition_loss_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T22:21:44.542747+00:00
-- url     : https://prove2.me/submissions/9284f9c2-83db-49a0-a468-dce3cd66b562

import Theorems.Thm_mme_child_partition_rate_sum_bound
import Theorems.Thm_mme_released_interior_child_card_bound

open scoped BigOperators
open MME MME.ReleasedInterior MME.RecursiveYZ

/-- The actual released child partition loses at most 540 times the common
error parameter, regardless of the partition chosen by extraction. -/
theorem solution
    (s : Fin 45) (nB nI : ℕ)
    (e : (Fin nB ⊕ Fin nI) ≃ Cell 4 6 (parent s))
    (q : Cell 4 6 (parent s) → ℝ)
    (b : Fin nB → ℝ) (i : Fin nI → ℝ)
    (scale delta bound : ℝ) (hscale : 0 ≤ scale) (hdelta : 0 ≤ delta)
    (hsum : bound ≤ ∑ c, q c)
    (hb : ∀ r, scale * (q (e (.inl r)) - 6 * delta) ≤ b r)
    (hi : ∀ r, scale * (q (e (.inr r)) - 6 * delta) ≤ i r) :
    scale * (bound - 540 * delta) ≤ (∑ r, b r) + ∑ r, i r := by
  have hcard : (Fintype.card (Cell 4 6 (parent s)) : ℝ) ≤ 90 := by
    exact_mod_cast mme_released_interior_child_card_bound s
  have hloss := mul_le_mul_of_nonneg_right hcard hdelta
  have hbase : bound - 540 * delta ≤
      (∑ c, q c) - (Fintype.card (Cell 4 6 (parent s)) : ℝ) * (6 * delta) := by
    nlinarith
  exact (mul_le_mul_of_nonneg_left hbase hscale).trans
    (mme_child_partition_rate_sum_bound nB nI e q b i scale (6 * delta) hb hi)


#print axioms solution
