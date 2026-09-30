-- Prove2me | solution 1 for lean_workbook_plus_80738
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:33:56.470305+00:00
-- url     : https://prove2.me/submissions/a44b2060-67d0-42cd-acc1-75044be3bef2

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution (x : ℝ) : (x^2 / (x^2 - x + 2) : ℝ) ≤ 8/7 := by
  have hd : 0 < x^2 - x + 2 := by nlinarith [sq_nonneg (x - 1/2)]
  apply (div_le_iff₀ hd).mpr
  nlinarith [sq_nonneg (x - 4)]
