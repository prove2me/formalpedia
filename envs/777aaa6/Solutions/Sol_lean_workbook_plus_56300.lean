-- Prove2me | solution 1 for lean_workbook_plus_56300
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:47:48.329715+00:00
-- url     : https://prove2.me/submissions/26665cdd-6cd4-4511-8a95-6043da2bbfd7

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed

theorem solution (x : ℝ) (hx : abs x < 1) :
  ∑' i : ℕ, x ^ i = 1 / (1 - x) := by
  rw [tsum_geometric_of_abs_lt_one hx, one_div]
