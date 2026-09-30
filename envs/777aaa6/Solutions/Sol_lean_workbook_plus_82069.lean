-- Prove2me | solution 1 for lean_workbook_plus_82069
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:18:41.608995+00:00
-- url     : https://prove2.me/submissions/03766c6c-9c3b-4c72-8d92-6d7c9c0b7559

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hxy : 0 < x ∧ 0 < y) :
    x + y + 1 / (x * y) ≤ 1 / x + 1 / y + x * y := by
  have hx0 : x ≠ 0 := ne_of_gt hxy.1
  have hy0 : y ≠ 0 := ne_of_gt hxy.2
  have hprod : 1 ≤ x * y := by nlinarith
  have hid : 1 / x + 1 / y + x * y - (x + y + 1 / (x * y)) =
      (x - 1) * (y - 1) * (x * y - 1) / (x * y) := by
    field_simp
    ring
  have hs : 0 ≤ (x - 1) * (y - 1) * (x * y - 1) / (x * y) :=
    div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
      (le_of_lt (mul_pos hxy.1 hxy.2))
  linarith
