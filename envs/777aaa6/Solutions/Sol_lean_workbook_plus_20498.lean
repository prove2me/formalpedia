-- Prove2me | solution 1 for lean_workbook_plus_20498
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:09:01.860022+00:00
-- url     : https://prove2.me/submissions/e8401ce7-5e24-49eb-82fa-45001fc91313

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℚ) (h₁ : a = 27 / 11) (h₂ : b = 2 + 5 / 11) (h₃ : c = 2 + 340 / 748) : a = b ∧ b = c := by
  subst h₁ h₂ h₃
  norm_num
