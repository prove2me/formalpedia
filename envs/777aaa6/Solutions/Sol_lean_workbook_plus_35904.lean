-- Prove2me | solution 1 for lean_workbook_plus_35904
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:42:49.098621+00:00
-- url     : https://prove2.me/submissions/84f405ed-41b3-48c9-8060-f57942a15f91

import Mathlib.Analysis.Complex.Basic

theorem solution (F : ℝ) (d : ℝ) (h₁ : F = 180) (h₂ : d = 6) : F * d = 1080 := by
  subst h₁ h₂
  norm_num
