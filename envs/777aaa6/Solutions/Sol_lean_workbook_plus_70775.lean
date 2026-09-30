-- Prove2me | solution 1 for lean_workbook_plus_70775
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:29:27.326702+00:00
-- url     : https://prove2.me/submissions/d9dc68d3-b996-4f2d-9fa6-81b65188e738

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0)
    (hab : a + b + c + d = 1) : a * b + b * c + c * d ≤ 1 / 4 := by
  nlinarith [sq_nonneg (a + c - (b + d)), mul_pos ha hd]
