-- Prove2me | solution 1 for lean_workbook_plus_36704
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:14:38.300672+00:00
-- url     : https://prove2.me/submissions/fa96856f-a92a-464d-8c77-a83ba8125653

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) : (a / (b - c) + b / (c - a) + c / (a - b) = 0) → (a / (b - c) ^ 2 + b / (c - a) ^ 2 + c / (a - b) ^ 2 = 0) := by
  intro h
  have h1 : b - c ≠ 0 := sub_ne_zero.mpr hbc
  have h2 : c - a ≠ 0 := sub_ne_zero.mpr hca
  have h3 : a - b ≠ 0 := sub_ne_zero.mpr hab
  have key : a / (b - c) ^ 2 + b / (c - a) ^ 2 + c / (a - b) ^ 2
      = (a / (b - c) + b / (c - a) + c / (a - b)) * (1 / (b - c) + 1 / (c - a) + 1 / (a - b)) := by
    field_simp
    ring
  rw [key, h, zero_mul]
