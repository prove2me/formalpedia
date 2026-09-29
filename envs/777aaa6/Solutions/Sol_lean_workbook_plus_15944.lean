-- Prove2me | solution 1 for lean_workbook_plus_15944
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:12:41.585012+00:00
-- url     : https://prove2.me/submissions/88704186-c6f2-4a35-8805-c578a9ccafc0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (ε : ℝ) (hε : 0 < ε) (a b c : ℝ) (hab : a = 1 + ε) (hbc : b = 1 + ε) (hca : c = 2) (h : a + b > c) : 3 * a ≥ b + c := by
  (intros; linarith)
