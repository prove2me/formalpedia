-- Prove2me | Theorems.Thm_avram_chat24_uniform_cell_cover_core
-- name    : avram_chat24_uniform_cell_cover_core
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:21:21.54512+00:00
-- url     : https://prove2.me/theorems/f5fbf1fa-ee0a-4483-aea6-f2ff492d1f5e
-- title:
--   avram_chat24_uniform_cell_cover_core
-- statement:
--   Automatically extracted helper theorem avram_chat24_uniform_cell_cover_core from oversized parent candidate 62347c3a2857c24662d5edb65fbdee2afae4561fe41c58af30436dabfbc40419.
-- source:
--   candidate-decomposition:966a885e-1f3b-4988-ade7-7c1ab4049f80:62347c3a2857c24662d5edb65fbdee2afae4561fe41c58af30436dabfbc40419

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable section
theorem avram_chat24_uniform_cell_cover_core (B : ℝ≥0) (hB : 0 < B) (n : ℕ)
    (t : ℝ≥0) (ht : 0 < t) (htB : t ≤ B) :
    ∃ i : ℕ, i < n + 1 ∧
      B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0) < t ∧
      t ≤ B * ((i + 1 : ℕ) : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0) := by sorry
end
