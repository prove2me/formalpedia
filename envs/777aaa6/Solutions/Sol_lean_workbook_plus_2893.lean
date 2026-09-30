-- Prove2me | solution 1 for lean_workbook_plus_2893
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:22:53.761791+00:00
-- url     : https://prove2.me/submissions/5d64dbea-947d-41ce-ae44-8b983e732f9b

import Mathlib

theorem solution (x : ℝ) (hx : 0 ≤ x ∧ x < 1) :
    ∑' n : ℕ, x ^ n = 1 / (1 - x) := by
  simpa only [one_div] using
    tsum_geometric_of_norm_lt_one (show ‖x‖ < 1 by simpa [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2)
