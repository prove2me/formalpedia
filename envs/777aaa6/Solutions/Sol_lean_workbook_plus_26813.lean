-- Prove2me | solution 1 for lean_workbook_plus_26813
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:24:27.296952+00:00
-- url     : https://prove2.me/submissions/a7652455-6fcc-4b7f-ad4c-623f8ea689fb

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (h : 1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) + 1 / (1 + c ^ 2) = 2) :
  a ^ 2 / (a ^ 2 + 1) + b ^ 2 / (b ^ 2 + 1) + c ^ 2 / (c ^ 2 + 1) = 1 := by
  have ha : (a ^ 2 + 1) ≠ 0 := by positivity
  have hb : (b ^ 2 + 1) ≠ 0 := by positivity
  have hc : (c ^ 2 + 1) ≠ 0 := by positivity
  have ea : a ^ 2 / (a ^ 2 + 1) = 1 - 1 / (1 + a ^ 2) := by
    field_simp
    ring
  have eb : b ^ 2 / (b ^ 2 + 1) = 1 - 1 / (1 + b ^ 2) := by
    field_simp
    ring
  have ec : c ^ 2 / (c ^ 2 + 1) = 1 - 1 / (1 + c ^ 2) := by
    field_simp
    ring
  rw [ea, eb, ec]
  linarith
