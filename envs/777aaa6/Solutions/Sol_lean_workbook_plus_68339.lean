-- Prove2me | solution 1 for lean_workbook_plus_68339
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:17:31.643457+00:00
-- url     : https://prove2.me/submissions/c975b73f-a04d-4393-b255-4e35a15d0ac1

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : a > 1) (hb : b > 1) :
    a ^ 2 / (b - 1) + b ^ 2 / (a - 1) ≥ 8 := by
  have h1 : a - 1 ≠ 0 := ne_of_gt (by linarith)
  have h2 : b - 1 ≠ 0 := ne_of_gt (by linarith)
  have hid : a ^ 2 / (b - 1) + b ^ 2 / (a - 1) - 8 =
      ((a + b - 2) * (a + b - 4) ^ 2 + 3 * (a + b + 2) * (a - b) ^ 2) /
        (4 * (a - 1) * (b - 1)) := by
    field_simp
    ring
  have ha' : 0 < a - 1 := by linarith
  have hb' : 0 < b - 1 := by linarith
  have hab : 0 < a + b - 2 := by linarith
  have hs : 0 ≤
      ((a + b - 2) * (a + b - 4) ^ 2 + 3 * (a + b + 2) * (a - b) ^ 2) /
        (4 * (a - 1) * (b - 1)) := by positivity
  linarith
