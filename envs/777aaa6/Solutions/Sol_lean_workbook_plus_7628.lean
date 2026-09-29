-- Prove2me | solution 1 for lean_workbook_plus_7628
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:58:47.739064+00:00
-- url     : https://prove2.me/submissions/08160561-c07f-423f-963f-3e70cb38df76

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ 0 := by
  (intros; positivity)
