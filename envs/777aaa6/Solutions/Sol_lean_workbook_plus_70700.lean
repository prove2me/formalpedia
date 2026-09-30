-- Prove2me | solution 1 for lean_workbook_plus_70700
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:54:24.253353+00:00
-- url     : https://prove2.me/submissions/01198c38-2b6a-4000-b78a-9eded800841d

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) (hab : a ∈ Set.Icc (-1) 1 ∧ b ∈ Set.Icc (-1) 1) :
    |a * b + 1| ≥ |a + b| := by
  rcases hab with ⟨⟨ha0, ha1⟩, ⟨hb0, hb1⟩⟩
  have hm := mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1)
  have hp := mul_nonneg (show 0 ≤ 1 + a by linarith) (show 0 ≤ 1 + b by linarith)
  apply le_trans (abs_le.mpr ?_) (le_abs_self (a * b + 1))
  constructor <;> nlinarith

#print axioms solution
