-- Prove2me | solution 1 for lean_workbook_plus_76597
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:34:00.680014+00:00
-- url     : https://prove2.me/submissions/78c42a2e-ee84-4efe-aaca-c838a32e9ae2

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1) :
    2 / (x + 3 * y) + 1 / (2 * x + y) ≥ 8 / 5 := by
  have h1 : 0 < x + 3 * y := by positivity
  have h2 : 0 < 2 * x + y := by positivity
  have hs : 0 < x + y := add_pos hx hy
  have hid : 2 / (x + 3 * y) + 1 / (2 * x + y) - 8 / (5 * (x + y)) =
      (3 * x - y)^2 / (5 * (x + y) * (x + 3 * y) * (2 * x + y)) := by
    field_simp [ne_of_gt h1, ne_of_gt h2, ne_of_gt hs]
    ring
  have hn : 0 ≤ (3 * x - y)^2 /
      (5 * (x + y) * (x + 3 * y) * (2 * x + y)) := by positivity
  have hbound : 8 / (5 * (x + y)) ≤ 2 / (x + 3 * y) + 1 / (2 * x + y) := by
    linarith only [hid, hn]
  simpa only [hxy, mul_one] using hbound
