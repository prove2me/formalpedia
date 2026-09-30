-- Prove2me | solution 1 for lean_workbook_plus_81217
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:28:24.579472+00:00
-- url     : https://prove2.me/submissions/c6b5b894-ff39-4f9d-8d8b-d7fe104e0cc0

import Mathlib

theorem solution (x : ℝ) (hx : x ≤ 1 / Real.sqrt 3) : 1 ≥ x * Real.sqrt 3 := by
  change x * Real.sqrt 3 ≤ 1
  exact (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mp hx
