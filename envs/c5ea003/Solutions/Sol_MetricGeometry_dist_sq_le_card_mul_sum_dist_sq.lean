-- Prove2me | solution 1 for MetricGeometry.dist_sq_le_card_mul_sum_dist_sq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T09:42:45.336086+00:00
-- url     : https://prove2.me/submissions/3075380e-7501-4b92-8dd2-814a05ffef1b

import Mathlib

universe u

theorem solution {X : Type u} [PseudoMetricSpace X] (x : ℕ → X) (n : ℕ) :
    dist (x 0) (x n) ^ 2
      ≤ (n : ℝ) * ∑ i ∈ Finset.range n, dist (x i) (x (i + 1)) ^ 2 := by
  have htel : dist (x 0) (x n) ≤ ∑ i ∈ Finset.range n, dist (x i) (x (i + 1)) :=
    dist_le_range_sum_dist x n
  have hcs : (∑ i ∈ Finset.range n, dist (x i) (x (i + 1))) ^ 2
      ≤ (Finset.range n).card * ∑ i ∈ Finset.range n, dist (x i) (x (i + 1)) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [Finset.card_range] at hcs
  refine le_trans ?_ hcs
  exact pow_le_pow_left₀ dist_nonneg htel 2
