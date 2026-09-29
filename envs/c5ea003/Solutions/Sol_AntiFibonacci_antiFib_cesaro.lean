-- Prove2me | solution 1 for AntiFibonacci.antiFib_cesaro
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T10:13:37.507892+00:00
-- url     : https://prove2.me/submissions/72c7793f-8b0e-4f7f-83a0-d2f688029416

import Mathlib
import Definitions.Def_Novelty_AntiFibonacciConnector

open Filter Topology

open AntiFibonacci

theorem antiFib_one_fb5 : ∀ n, antiFib n = 1
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      simp only [antiFib, leastPositiveAvoidingSum, antiFib_one_fb5 (n + 1), antiFib_one_fb5 n]
      norm_num

theorem solution : ¬ Filter.Tendsto (fun n : ℕ => (∑ k ∈ Finset.range (n + 1), (antiFib k : ℝ)) / (n : ℝ) ^ 3)
      Filter.atTop (𝓝 (1 / 6)) := by
  intro h
  have hsum : ∀ n : ℕ, (∑ k ∈ Finset.range (n + 1), (antiFib k : ℝ)) = (n : ℝ) + 1 := by
    intro n
    simp [antiFib_one_fb5]
  have h0 : Filter.Tendsto (fun n : ℕ => (∑ k ∈ Finset.range (n + 1), (antiFib k : ℝ)) / (n : ℝ) ^ 3)
      Filter.atTop (𝓝 0) := by
    simp_rw [hsum]
    have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (n : ℝ) ^ 3) atTop (𝓝 0) := by
      have ha : Filter.Tendsto (fun n : ℕ => 1 / (n : ℝ) ^ 2 + 1 / (n : ℝ) ^ 3) atTop (𝓝 0) := by
        have e2 : Filter.Tendsto (fun n : ℕ => 1 / (n : ℝ) ^ 2) atTop (𝓝 0) := by
          simpa using (tendsto_pow_atTop (n := 2) (by norm_num)).comp tendsto_natCast_atTop_atTop |>.inv_tendsto_atTop
        have e3 : Filter.Tendsto (fun n : ℕ => 1 / (n : ℝ) ^ 3) atTop (𝓝 0) := by
          simpa using (tendsto_pow_atTop (n := 3) (by norm_num)).comp tendsto_natCast_atTop_atTop |>.inv_tendsto_atTop
        simpa using e2.add e3
      refine ha.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have : (n : ℝ) ≠ 0 := by positivity
      field_simp
    exact h1
  have := tendsto_nhds_unique h h0
  norm_num at this

