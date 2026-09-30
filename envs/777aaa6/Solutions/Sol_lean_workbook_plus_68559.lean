-- Prove2me | solution 1 for lean_workbook_plus_68559
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:18:40.858436+00:00
-- url     : https://prove2.me/submissions/2e95bbf1-ad2b-4de7-a390-3fa48dc4235b

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) ≥ 2 / (1 + a * b) := by
  have ha' : 0 < a := by linarith
  have hb' : 0 < b := by linarith
  have hab : 1 ≤ a * b := by nlinarith
  have h1 : 1 + a ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have h2 : 1 + b ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have h3 : 1 + a * b ≠ 0 := ne_of_gt (by positivity)
  have hid : 1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) - 2 / (1 + a * b) =
      (a * b - 1) * (a - b) ^ 2 / ((1 + a ^ 2) * (1 + b ^ 2) * (1 + a * b)) := by
    field_simp
    ring
  have hs : 0 ≤ (a * b - 1) * (a - b) ^ 2 /
      ((1 + a ^ 2) * (1 + b ^ 2) * (1 + a * b)) :=
    div_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by positivity)
  linarith
