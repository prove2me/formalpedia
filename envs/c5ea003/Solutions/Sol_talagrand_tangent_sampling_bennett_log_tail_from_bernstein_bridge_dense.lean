-- Prove2me | solution 1 for talagrand_tangent_sampling_bennett_log_tail_from_bernstein_bridge_dense
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-25T03:47:08.428065+00:00
-- url     : https://prove2.me/submissions/38573dce-7c37-4de2-b475-4b83119a741a

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

theorem solution
    (u : ℝ) :
    0 ≤ u →
    u ^ 2 / (2 + 2 * u / 3) ≤ (1 + u) * Real.log (1 + u) - u := by
  intro hu
  have hu2 : 0 < u + 2 := by linarith
  have hu3 : 0 < u + 3 := by linarith
  have honeu : 0 ≤ 1 + u := by linarith
  have hlog :
      (∑ k ∈ Finset.range 2,
          (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) *
            (u / (u + 2)) ^ (2 * k + 1)) ≤ Real.log (1 + u) := by
    exact sum_le_hasSum (Finset.range 2)
      (by
        intro k hk
        positivity)
      (Real.hasSum_log_one_add hu)
  have hmul :
      (1 + u) *
          (∑ k ∈ Finset.range 2,
            (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) *
              (u / (u + 2)) ^ (2 * k + 1)) ≤
        (1 + u) * Real.log (1 + u) :=
    mul_le_mul_of_nonneg_left hlog honeu
  have halg :
      u ^ 2 / (2 + 2 * u / 3) ≤
        (1 + u) *
          (∑ k ∈ Finset.range 2,
            (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) *
              (u / (u + 2)) ^ (2 * k + 1)) - u := by
    have hden2 : u + 2 ≠ 0 := ne_of_gt hu2
    have hden3 : u + 3 ≠ 0 := ne_of_gt hu3
    have hdenB : 2 + 2 * u / 3 ≠ 0 := by positivity
    have hsum :
        (∑ k ∈ Finset.range 2,
          (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) *
            (u / (u + 2)) ^ (2 * k + 1)) =
          2 * u / (u + 2) + (2 / 3) * (u / (u + 2)) ^ 3 := by
      norm_num [Finset.sum_range_succ]
      ring
    have hdiff :
        ((1 + u) *
            (∑ k ∈ Finset.range 2,
              (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) *
                (u / (u + 2)) ^ (2 * k + 1)) - u) -
          u ^ 2 / (2 + 2 * u / 3) =
            u ^ 4 * (u + 4) / (6 * (u + 2) ^ 3 * (u + 3)) := by
      rw [hsum]
      field_simp [hden2, hden3, hdenB]
      ring
    have hnonneg :
        0 ≤ u ^ 4 * (u + 4) / (6 * (u + 2) ^ 3 * (u + 3)) := by
      positivity
    nlinarith
  linarith
