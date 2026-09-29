-- Prove2me | solution 1 for lean_workbook_plus_7175
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:06:01.515912+00:00
-- url     : https://prove2.me/submissions/19de86df-e057-4011-8d6b-d856515d9602

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c x y z : ℝ) : x = (4 * a + 2 * b + c) / 7 ∧ y = (a + 4 * b + 2 * c) / 7 ∧ z = (2 * a + b + 4 * c) / 7 ↔ x = (4 * a + 2 * b + c) / 7 ∧ y = (a + 4 * b + 2 * c) / 7 ∧ z = (2 * a + b + 4 * c) / 7 := by
  norm_num
