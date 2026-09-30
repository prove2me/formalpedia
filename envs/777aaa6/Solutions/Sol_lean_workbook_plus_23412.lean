-- Prove2me | solution 1 for lean_workbook_plus_23412
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T01:18:39.272179+00:00
-- url     : https://prove2.me/submissions/8cfd9050-cc5a-4450-83b5-e04a90c45807

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) (x y : ℝ) (hx : x > 0) (hy : y > x) : (x:ℝ) ^ (1 / n) - (y:ℝ) ^ (1 / n) ≤ (y - x:ℝ) ^ (1 / n) := by
  rcases n with _ | _ | n
  · simp
  · simp
    linarith
  · have h0 : 1 / (n + 1 + 1) = 0 := Nat.div_eq_of_lt (by omega)
    rw [h0]
    simp
