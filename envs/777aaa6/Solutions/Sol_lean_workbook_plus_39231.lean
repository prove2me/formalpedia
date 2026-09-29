-- Prove2me | solution 1 for lean_workbook_plus_39231
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:16:56.295671+00:00
-- url     : https://prove2.me/submissions/4f2407e6-526a-45c7-b3df-afce8293f1d4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h : 3 > 0 ∧ 2 > 0 ∧ 1 > 0) : (Nat.choose 3 1 * Nat.choose 2 1 * Nat.choose 1 1) = 6 := by
  norm_num
