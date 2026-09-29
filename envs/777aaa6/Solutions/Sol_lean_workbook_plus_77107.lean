-- Prove2me | solution 1 for lean_workbook_plus_77107
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T06:20:50.291647+00:00
-- url     : https://prove2.me/submissions/23241d85-5c21-429f-976c-01a0ccde1f17

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ n : ℕ, ∃ a b c : ℚ, a + b + c = a * b * c ∧ a * b * c = 6 := by
  intro n
  exact ⟨1, 2, 3, by norm_num⟩
