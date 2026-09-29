-- Prove2me | solution 1 for lean_workbook_plus_5851
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:55.989939+00:00
-- url     : https://prove2.me/submissions/2fe93881-ddc8-4a64-b520-26cb272c7a5e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x:ℝ) : (x - 1) ^ 2 * (x ^ 2 + x + 1) ≥ 0 := by
  apply mul_nonneg (sq_nonneg _)
  nlinarith [sq_nonneg (2*x+1)]
