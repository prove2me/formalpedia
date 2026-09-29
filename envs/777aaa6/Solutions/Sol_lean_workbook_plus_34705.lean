-- Prove2me | solution 1 for lean_workbook_plus_34705
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:37:51.695891+00:00
-- url     : https://prove2.me/submissions/186de1c1-e6dd-4d43-ae62-f2c597178470

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (x : ℝ) : x ^ 4 + x ^ 3 - x + 1 > 0 := by
  have h : (0:ℝ) ≤ (x^2+x/2-1)^2 := sq_nonneg _
  have h2 : (0:ℝ) ≤ (x+2)^2 := sq_nonneg _
  nlinarith [sq_nonneg (x^2-1), sq_nonneg (x-1)]
