-- Prove2me | solution 1 for lean_workbook_plus_35162
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:42:19.623286+00:00
-- url     : https://prove2.me/submissions/175fc2d6-f692-4071-b13e-ee4bb6509833

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (h : x > 1) : 3 * x - 1 > x + 1 := by
  (intros; linarith)
