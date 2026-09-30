-- Prove2me | solution 1 for lean_workbook_plus_45833
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:41:01.817749+00:00
-- url     : https://prove2.me/submissions/49524aac-3de9-4051-b1fe-b5e9135cc693

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (h : a * b + b * c + c * a = 3) : a ^ 2 + b ^ 2 + c ^ 2 + 3 ≥ 2 * (a + b + c) := by
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
