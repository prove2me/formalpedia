-- Prove2me | solution 1 for lean_workbook_plus_68662
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:51:57.819459+00:00
-- url     : https://prove2.me/submissions/91fd5584-6783-41db-8c87-038538cc54e2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : √(a^2 + b^2) + √(b^2 + c^2) + √(c^2 + a^2) ≥ a + b + c := by
  have hab : a ≤ Real.sqrt (a^2+b^2) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ a^2+b^2 by positivity), Real.sqrt_nonneg (a^2+b^2), sq_nonneg b]
  have hbc : b ≤ Real.sqrt (b^2+c^2) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ b^2+c^2 by positivity), Real.sqrt_nonneg (b^2+c^2), sq_nonneg c]
  have hca : c ≤ Real.sqrt (c^2+a^2) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ c^2+a^2 by positivity), Real.sqrt_nonneg (c^2+a^2), sq_nonneg a]
  linarith
