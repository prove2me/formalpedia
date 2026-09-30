-- Prove2me | solution 1 for lean_workbook_plus_79601
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:06:07.193978+00:00
-- url     : https://prove2.me/submissions/ac581916-34cc-4d8f-9d4b-0ff767cc9d87

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (a * b + a + 1) + b / (b * c + b + 1) + c / (c * a + c + 1) ≤ 1 := by
  have h1 : a * b + a + 1 ≠ 0 := ne_of_gt (by positivity)
  have h2 : b * c + b + 1 ≠ 0 := ne_of_gt (by positivity)
  have h3 : c * a + c + 1 ≠ 0 := ne_of_gt (by positivity)
  have hid : 1 - (a / (a * b + a + 1) + b / (b * c + b + 1) +
      c / (c * a + c + 1)) =
      (a * b * c - 1) ^ 2 / ((a * b + a + 1) * (b * c + b + 1) * (c * a + c + 1)) := by
    field_simp
    ring
  have hnonneg : 0 ≤ (a * b * c - 1) ^ 2 /
      ((a * b + a + 1) * (b * c + b + 1) * (c * a + c + 1)) := by positivity
  linarith
