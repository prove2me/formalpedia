-- Prove2me | solution 1 for lean_workbook_plus_27806
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:41:44.932679+00:00
-- url     : https://prove2.me/submissions/73b63a68-13c6-4005-9350-c31dbc0c1b97

import Mathlib

set_option autoImplicit false

theorem solution (x y : Real) (hx : 0 < x) (hy : 0 < y) :
    1 / (1 + x) ^ 2 + 1 / (1 + y) ^ 2 ≥ 1 / (1 + x * y) := by
  have hx1 : 1 + x ≠ 0 := by positivity
  have hy1 : 1 + y ≠ 0 := by positivity
  have hxy1 : 1 + x * y ≠ 0 := by positivity
  have hid : 1 / (1 + x) ^ 2 + 1 / (1 + y) ^ 2 - 1 / (1 + x * y) =
      ((x * y - 1) ^ 2 + x * y * (x - y) ^ 2) /
        ((1 + x) ^ 2 * (1 + y) ^ 2 * (1 + x * y)) := by
    field_simp
    ring
  have hn : 0 ≤ (x * y - 1) ^ 2 + x * y * (x - y) ^ 2 := by positivity
  have hd : 0 < (1 + x) ^ 2 * (1 + y) ^ 2 * (1 + x * y) := by positivity
  have hdiff : 0 ≤ 1 / (1 + x) ^ 2 + 1 / (1 + y) ^ 2 - 1 / (1 + x * y) := by
    rw [hid]
    exact div_nonneg hn hd.le
  linarith

#print axioms solution
