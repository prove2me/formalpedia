-- Prove2me | solution 1 for lean_workbook_plus_8193
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:56:07.466166+00:00
-- url     : https://prove2.me/submissions/e0e3c807-6c99-4a8e-8157-7280560f4690

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution (a b c : ℂ) (h : a + b + c = 0) : a ^ 3 + b ^ 3 + c ^ 3 = 3 * a * b * c := by
  have hc : c = -a - b := by linear_combination h
  rw [hc]
  ring
