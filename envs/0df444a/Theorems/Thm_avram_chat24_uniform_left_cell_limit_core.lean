-- Prove2me | Theorems.Thm_avram_chat24_uniform_left_cell_limit_core
-- name    : avram_chat24_uniform_left_cell_limit_core
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:44:09.117222+00:00
-- url     : https://prove2.me/theorems/977d6566-a376-446c-9fdf-c3488477439a
-- title:
--   avram_chat24_uniform_left_cell_limit_core
-- statement:
--   Automatically extracted helper theorem avram_chat24_uniform_left_cell_limit_core from oversized parent candidate 0b83abe0454696609736288e6dac3c047d97baf0381e61d7d9f4afd1b18ed527.
-- source:
--   candidate-decomposition:966a885e-1f3b-4988-ade7-7c1ab4049f80:0b83abe0454696609736288e6dac3c047d97baf0381e61d7d9f4afd1b18ed527

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable section
theorem avram_chat24_uniform_left_cell_limit_core (B : ℝ≥0) (hB : 0 < B)
    (t : ℝ≥0) (ht : 0 < t) (htB : t ≤ B) :
    let u : ℕ → ℕ → ℝ≥0 := fun n i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    ∃ k : ℕ → ℕ,
      (∀ n, k n < n + 1 ∧ u n (k n) < t ∧ t ≤ u n (k n + 1)) ∧
      (∀ n j, u n j < t → t ≤ u n (j + 1) → j = k n) ∧
      Tendsto (fun n => u n (k n)) atTop (𝓝[<] t) := by sorry
end
