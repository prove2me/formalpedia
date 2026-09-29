-- Prove2me | solution 1 for lean_workbook_plus_69089
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:40:16.915377+00:00
-- url     : https://prove2.me/submissions/01f5860c-a849-4b73-99ff-7c4199b78b8d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Sqrt

set_option autoImplicit false

theorem solution (x : ℝ) (hx : 0 < x ∧ x < 3) : 1 + 2 * Real.sqrt x ≥ x := by
  have hs := Real.sq_sqrt hx.1.le
  have hn := Real.sqrt_nonneg x
  by_cases h : x ≤ 1
  · linarith
  · have hroot : 1 ≤ Real.sqrt x := by nlinarith
    linarith [hx.2]
