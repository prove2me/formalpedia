-- Prove2me | solution 1 for lean_workbook_plus_31539
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:18:18.100454+00:00
-- url     : https://prove2.me/submissions/cf39109a-66f0-4abc-9163-e0459f16d1b5

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c d : ℝ) (hab : 1 ≤ a ∧ a ≤ 3) (hbc : 1 ≤ b ∧ b ≤ 3) (hcd : 1 ≤ c ∧ c ≤ 3) : (a - 1) * (b - 1) * (c - 1) ≥ 0 ∧ (3 - a) * (3 - b) * (3 - c) ≥ 0 := by
  constructor
  · exact mul_nonneg (mul_nonneg (by linarith [hab.1]) (by linarith [hbc.1])) (by linarith [hcd.1])
  · exact mul_nonneg (mul_nonneg (by linarith [hab.2]) (by linarith [hbc.2])) (by linarith [hcd.2])
