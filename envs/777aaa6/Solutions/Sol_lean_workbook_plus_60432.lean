-- Prove2me | solution 1 for lean_workbook_plus_60432
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:44:42.106151+00:00
-- url     : https://prove2.me/submissions/05a195fd-c8fe-4ec3-8bd9-9f4b6b8d71d8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (habc : a * b * c ≥ 2^9) (ha : a ≥ 1) (hb : b ≥ 1) (hc : c ≥ 1) : a + b + c ≥ 3 := by
  (intros; linarith)
