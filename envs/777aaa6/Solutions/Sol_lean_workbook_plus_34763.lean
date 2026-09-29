-- Prove2me | solution 1 for lean_workbook_plus_34763
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:17:14.534587+00:00
-- url     : https://prove2.me/submissions/ad65fb10-c878-4532-a415-60f8a4fb0c8d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) = 2 / 3) : a + b + c + 2 ≥ 560 / 729 * a * b * c := by
  (intros; linarith)
