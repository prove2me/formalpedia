-- Prove2me | solution 1 for lean_workbook_plus_72787
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:40:22.044684+00:00
-- url     : https://prove2.me/submissions/56e46a16-5323-46f7-8e90-6e676cba529b

import Mathlib
set_option autoImplicit false

theorem solution (b : ℝ) (h₀ : 0 < b)
    (h₁ : 2 / (1 / 40 + 1 / b) = 30) : b = 24 := by
  have hd : 0 < (1 : ℝ) / 40 + 1 / b := by positivity
  have h := (div_eq_iff hd.ne').mp h₁
  field_simp at h
  nlinarith

#print axioms solution
