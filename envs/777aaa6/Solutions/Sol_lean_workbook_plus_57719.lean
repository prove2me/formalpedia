-- Prove2me | solution 1 for lean_workbook_plus_57719
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:44:15.977285+00:00
-- url     : https://prove2.me/submissions/0970217c-d1a8-434b-af06-174499209be1

import Mathlib.Analysis.Complex.Basic

theorem solution  (a b c d : ℝ)
  (h₀ : a = 1)
  (h₁ : b = 25)
  (h₂ : c = 17)
  (h₃ : d = 81) :
  (a + b + c + d) / 4 = 31 := by
  subst h₀ h₁ h₂ h₃
  norm_num
