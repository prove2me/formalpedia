-- Prove2me | solution 1 for RybinAI2026.P01.fractional_kernel_pointwise_order
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T02:35:37.435983+00:00
-- url     : https://prove2.me/submissions/c35b1c05-874b-4edf-9988-549a94824d8c

import Mathlib

theorem solution (u v r : ℝ)
    (hu : 0 < u) (huv : u ≤ v) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    u / (2 * r * (1 - r) + u * (r ^ 2 + (1 - r) ^ 2)) ≤
        v / (2 * r * (1 - r) + v * (r ^ 2 + (1 - r) ^ 2)) ∧
      (1 + v) / (2 * r * (1 - r) + v * (r ^ 2 + (1 - r) ^ 2)) ≤
        (1 + u) / (2 * r * (1 - r) + u * (r ^ 2 + (1 - r) ^ 2)) := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have h1r : 0 ≤ 1 - r := sub_nonneg.mpr hr.2
  have hbase : 0 ≤ 2 * r * (1 - r) :=
    mul_nonneg (mul_nonneg (by norm_num) hr.1) h1r
  have hq : 0 < r ^ 2 + (1 - r) ^ 2 := by
    nlinarith [sq_nonneg (2 * r - 1)]
  have hdu : 0 < 2 * r * (1 - r) + u * (r ^ 2 + (1 - r) ^ 2) :=
    add_pos_of_nonneg_of_pos hbase (mul_pos hu hq)
  have hdv : 0 < 2 * r * (1 - r) + v * (r ^ 2 + (1 - r) ^ 2) :=
    add_pos_of_nonneg_of_pos hbase (mul_pos hv hq)
  constructor
  · rw [div_le_div_iff₀ hdu hdv]
    have hrem := mul_nonneg hbase (sub_nonneg.mpr huv)
    nlinarith
  · rw [div_le_div_iff₀ hdv hdu]
    have hgap : 0 ≤ r ^ 2 + (1 - r) ^ 2 - 2 * r * (1 - r) := by
      nlinarith [sq_nonneg (2 * r - 1)]
    have hrem := mul_nonneg hgap (sub_nonneg.mpr huv)
    nlinarith
