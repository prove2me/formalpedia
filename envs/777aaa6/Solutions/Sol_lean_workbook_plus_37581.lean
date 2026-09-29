-- Prove2me | solution 1 for lean_workbook_plus_37581
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:53:25.846907+00:00
-- url     : https://prove2.me/submissions/c89e2347-9ee3-48d5-bfea-ac52e88a881a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a c : ℝ) (h : c + a = 1) : c + a = 1 := by
  (intros; simp_all)
