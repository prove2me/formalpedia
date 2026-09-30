-- Prove2me | solution 1 for lean_workbook_plus_69971
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:21:52.163283+00:00
-- url     : https://prove2.me/submissions/31856ea4-2fbe-4fad-9c2c-d12b0638ad4c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

theorem solution (k a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : k * (a + b) = 1 + a * b) (hk : 1 ≤ k) :
    a + b + 1 / a + 1 / b ≥ 4 * k := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hscaled := congrArg (fun t : ℝ => t * (a + b)) hab
  have hid : a + b + 1 / a + 1 / b - 4 * k = k * (a - b) ^ 2 / (a * b) := by
    field_simp
    nlinarith [hscaled]
  have hs : 0 ≤ k * (a - b) ^ 2 / (a * b) := by positivity
  linarith
