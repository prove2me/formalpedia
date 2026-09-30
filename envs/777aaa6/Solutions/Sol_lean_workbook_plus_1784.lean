-- Prove2me | solution 1 for lean_workbook_plus_1784
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:27:35.824538+00:00
-- url     : https://prove2.me/submissions/3689cd8d-6835-4dcc-b83e-e466bfc13975

import Mathlib

theorem solution (x : ℝ) (h₀ : ∑' k : ℕ, (7 / (2 ^ k)) = x) : x = 14 := by
  have hs : HasSum (fun k : ℕ => (1 / 2 : ℝ) ^ k) 2 := by
    convert hasSum_geometric_of_abs_lt_one (r := (1 / 2 : ℝ)) (by norm_num) using 1 <;>
      norm_num
  calc
    x = ∑' k : ℕ, 7 / (2 ^ k) := h₀.symm
    _ = ∑' k : ℕ, 7 * (1 / 2 : ℝ) ^ k := by
      apply tsum_congr
      intro k
      simp [div_eq_mul_inv, inv_pow]
    _ = 7 * 2 := (hs.mul_left 7).tsum_eq
    _ = 14 := by norm_num
