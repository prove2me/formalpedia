-- Prove2me | solution 1 for lean_workbook_plus_71601
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:51:43.803286+00:00
-- url     : https://prove2.me/submissions/890f73ea-f7b7-4fda-bcc0-188ad4949b36

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) :
  x * (2 / 3 - x) + (1 - x) * (x - 1 / 2) = -2 * x^2 + (13 / 6) * x - 1 / 2 := by
  (intros; linarith)
