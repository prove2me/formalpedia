-- Prove2me | solution 1 for lean_workbook_plus_26895
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:00:43.734011+00:00
-- url     : https://prove2.me/submissions/f3d5ccbd-dcb3-456c-a6a7-44d02efd7417

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

theorem solution (x y z : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h : 1 / x + 1 / y + 1 / z = 0) :
    y * z / x ^ 2 + z * x / y ^ 2 + x * y / z ^ 2 = 3 := by
  field_simp [hx, hy, hz] at h ⊢
  linear_combination
    ((y * z) ^ 2 + (x * z) ^ 2 + (x * y) ^ 2 -
      (y * z) * (x * z) - (y * z) * (x * y) - (x * z) * (x * y)) * h
