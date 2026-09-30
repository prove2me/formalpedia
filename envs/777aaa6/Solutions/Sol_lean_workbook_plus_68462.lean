-- Prove2me | solution 1 for lean_workbook_plus_68462
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:24:15.297834+00:00
-- url     : https://prove2.me/submissions/953d61ed-7328-43f2-b1e8-97a17f77b13e

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1) :
    a / (2 * b + c) + b / (2 * c + a) + c / (2 * a + b) ≥ 1 := by
  rcases ha with ⟨ha, hb, hc, habc⟩
  have h1 : 2 * b + c ≠ 0 := ne_of_gt (by positivity)
  have h2 : 2 * c + a ≠ 0 := ne_of_gt (by positivity)
  have h3 : 2 * a + b ≠ 0 := ne_of_gt (by positivity)
  have hid : a / (2 * b + c) + b / (2 * c + a) + c / (2 * a + b) - 1 =
      ((a - b) ^ 2 * (11 * a + b + 3 * c) +
        (b - c) ^ 2 * (11 * b + c + 3 * a) +
        (c - a) ^ 2 * (11 * c + a + 3 * b)) /
          (6 * (2 * b + c) * (2 * c + a) * (2 * a + b)) := by
    field_simp
    ring
  have hs : 0 ≤ ((a - b) ^ 2 * (11 * a + b + 3 * c) +
      (b - c) ^ 2 * (11 * b + c + 3 * a) +
      (c - a) ^ 2 * (11 * c + a + 3 * b)) /
        (6 * (2 * b + c) * (2 * c + a) * (2 * a + b)) := by positivity
  linarith
