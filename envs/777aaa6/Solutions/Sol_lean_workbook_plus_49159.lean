-- Prove2me | solution 1 for lean_workbook_plus_49159
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:37:01.732763+00:00
-- url     : https://prove2.me/submissions/4210625d-765f-43ad-b7ae-3156b1ed4775

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : 10 + 24 > x → x < 34 ∧ 10 + x > 24 → x > 14 := by
  (intros; linarith)
