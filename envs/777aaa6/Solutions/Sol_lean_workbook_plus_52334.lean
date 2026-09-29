-- Prove2me | solution 1 for lean_workbook_plus_52334
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:04:49.010623+00:00
-- url     : https://prove2.me/submissions/36aea5ab-c97a-4c42-bc27-34f2a6642ca8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (s c b : ℝ)
  (h₀ : 4 * s + c + 10 * b = 16.9)
  (h₁ : 3 * s + c + 7 * b = 12.6) :
  2 * s + 2 * c + 2 * b = 8 := by
  (intros; linarith)
