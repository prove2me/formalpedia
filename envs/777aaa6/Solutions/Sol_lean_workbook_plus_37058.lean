-- Prove2me | solution 1 for lean_workbook_plus_37058
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:42:22.499036+00:00
-- url     : https://prove2.me/submissions/4804e912-4d88-4d19-a981-122dfe665fa2

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (a / (b + c) + 1 / 2) + 1 / (b / (c + a) + 1 / 4) + 1 / (c / (a + b) + 1 / 2)) ≥ 16 / 5 := by
  have hs : 0 < a + b + c := by linarith
  have hbc : 0 < b + c := by linarith
  have hca : 0 < c + a := by linarith
  have hab : 0 < a + b := by linarith
  have h1 : 1 / (a / (b + c) + 1 / 2) = 2 * (b + c) / (2 * a + b + c) := by
    field_simp
    ring
  have h2 : 1 / (b / (c + a) + 1 / 4) = 4 * (c + a) / (4 * b + c + a) := by
    field_simp
    ring
  have h3 : 1 / (c / (a + b) + 1 / 2) = 2 * (a + b) / (a + b + 2 * c) := by
    field_simp
    ring
  have e1 : 2 * (b + c) / (2 * a + b + c) - (46 / 25 - 64 * a / (25 * (a + b + c)))
      = 4 * (3 * a - b - c) ^ 2 / (25 * (a + b + c) * (2 * a + b + c)) := by
    field_simp
    ring
  have e2 : 4 * (c + a) / (4 * b + c + a) - (52 / 25 - 64 * b / (25 * (a + b + c)))
      = 48 * (b - c - a) ^ 2 / (25 * (a + b + c) * (4 * b + c + a)) := by
    field_simp
    ring
  have e3 : 2 * (a + b) / (a + b + 2 * c) - (46 / 25 - 64 * c / (25 * (a + b + c)))
      = 4 * (3 * c - a - b) ^ 2 / (25 * (a + b + c) * (a + b + 2 * c)) := by
    field_simp
    ring
  have p1 : 0 ≤ 4 * (3 * a - b - c) ^ 2 / (25 * (a + b + c) * (2 * a + b + c)) := by positivity
  have p2 : 0 ≤ 48 * (b - c - a) ^ 2 / (25 * (a + b + c) * (4 * b + c + a)) := by positivity
  have p3 : 0 ≤ 4 * (3 * c - a - b) ^ 2 / (25 * (a + b + c) * (a + b + 2 * c)) := by positivity
  have hsum : 64 * a / (25 * (a + b + c)) + 64 * b / (25 * (a + b + c)) + 64 * c / (25 * (a + b + c)) = 64 / 25 := by
    field_simp
  rw [h1, h2, h3]
  linarith
