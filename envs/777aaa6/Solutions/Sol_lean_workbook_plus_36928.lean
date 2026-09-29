-- Prove2me | solution 1 for lean_workbook_plus_36928
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:54:20.455861+00:00
-- url     : https://prove2.me/submissions/27f30f20-3e21-4e22-832f-6621c98a5dfd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x = ∑' k : ℕ, (Real.sqrt (5 + Real.sqrt (5 + Real.sqrt (5 - Real.sqrt (5 + Real.sqrt (5 + Real.sqrt (5 + ↑k)))))))) : ∃ y, y = (2 + Real.sqrt 5) / 2 + (Real.sqrt (15 - 6 * Real.sqrt 5)) / 2 := by
  norm_num
