-- Prove2me | solution 1 for lean_workbook_plus_66534
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:32:29.364128+00:00
-- url     : https://prove2.me/submissions/e51e482f-87d6-4613-a33d-ff1effdc6556

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 + b^2 + c^2 + (a + b + c)^2 ≥ (a + b)^2 + (b + c)^2 + (c + a)^2 := by
  (intros; linarith)
