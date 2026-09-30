-- Prove2me | solution 1 for lean_workbook_plus_31673
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:14:23.641087+00:00
-- url     : https://prove2.me/submissions/8092b3c9-6ae3-437d-ac41-fb4d6f30468a

import Mathlib.Analysis.Complex.Basic

theorem solution (a : ℝ) (ha : 1 < a) : a^2 / (a - 1) ≥ 4 := by
  rw [ge_iff_le, le_div_iff₀ (by linarith)]
  nlinarith [sq_nonneg (a - 2)]
