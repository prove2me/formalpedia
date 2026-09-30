-- Prove2me | solution 1 for lean_workbook_plus_8407
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:11:56.199393+00:00
-- url     : https://prove2.me/submissions/2df02179-cadc-402e-a766-bbac72ff79cd

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) : a ^ 2 + b ^ 2 ≥ a * b := by
  nlinarith [sq_nonneg (a - b), sq_nonneg a, sq_nonneg b]
