-- Prove2me | solution 1 for lean_workbook_plus_68371
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:19:59.173252+00:00
-- url     : https://prove2.me/submissions/c8b5058e-6fab-4127-a73b-801c26eb0ccf

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution (a b x y : ℝ) (hx : x > 0) (hy : y > 0) :
    a ^ 2 / x + b ^ 2 / y ≥ (a + b) ^ 2 / (x + y) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hxy0 : x + y ≠ 0 := ne_of_gt (add_pos hx hy)
  have hid : a ^ 2 / x + b ^ 2 / y - (a + b) ^ 2 / (x + y) =
      (a * y - b * x) ^ 2 / (x * y * (x + y)) := by
    field_simp
    ring
  have hs : 0 ≤ (a * y - b * x) ^ 2 / (x * y * (x + y)) := by positivity
  linarith
