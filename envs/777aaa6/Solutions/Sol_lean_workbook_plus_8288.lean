-- Prove2me | solution 1 for lean_workbook_plus_8288
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:56:08.94162+00:00
-- url     : https://prove2.me/submissions/b781f504-98f1-40b9-b1e8-df570e06eaf0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (a : ℝ) (ha : 0 < a) : (a^2 / (a + 1)) ≥ (3/4 * a - 1/4) := by
  apply (le_div_iff₀ (by linarith : 0 < a + 1)).mpr
  nlinarith [sq_nonneg (a - 1)]
