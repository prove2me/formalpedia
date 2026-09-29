-- Prove2me | solution 1 for lean_workbook_plus_38504
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:52:02.408044+00:00
-- url     : https://prove2.me/submissions/ff818057-9025-452e-997f-9b46343cefc1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c : ℝ} : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ 0 := by
  (intros; positivity)
