-- Prove2me | solution 1 for lean_workbook_plus_29099
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:04:45.311111+00:00
-- url     : https://prove2.me/submissions/af7665cd-c172-4600-a64b-4f224209bff7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c : ℝ} (h : a + b + c = 4) : a / 4 + b / 4 + c / 4 = 1 := by
  (intros; linarith)
