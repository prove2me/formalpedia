-- Prove2me | solution 1 for lean_workbook_plus_8103
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:44:16.950161+00:00
-- url     : https://prove2.me/submissions/15033ec3-90dc-4a86-8760-a36e2cecb2be

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c k : ℝ) (h : k > 0) : (1 + k) * (a ^ 4 + b ^ 4 + c ^ 4) ≥ a ^ 2 * b ^ 2 + (b ^ 2 + a ^ 2) * c ^ 2 := by
  have hs : a ^ 4 + b ^ 4 + c ^ 4 ≥ 0 := by positivity
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2),
    mul_nonneg h.le hs]
