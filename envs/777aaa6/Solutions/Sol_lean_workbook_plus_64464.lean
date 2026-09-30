-- Prove2me | solution 1 for lean_workbook_plus_64464
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:27:01.445963+00:00
-- url     : https://prove2.me/submissions/87882bc8-0202-4935-9d1f-ebeef41a7097

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed

theorem solution : ∀ x : ℝ, |x| < 1 → 1 / (1 - x) = ∑' k : ℕ, x ^ k := by
  intro x hx
  rw [tsum_geometric_of_abs_lt_one hx, one_div]
