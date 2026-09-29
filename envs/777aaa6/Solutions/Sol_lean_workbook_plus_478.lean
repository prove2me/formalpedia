-- Prove2me | solution 1 for lean_workbook_plus_478
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:51:27.182081+00:00
-- url     : https://prove2.me/submissions/770f029c-3c4d-46c6-bd82-a5945dea7d99

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (habc : a * b * c = 1) (h : a^3 + b^3 + c^3 + d^3 ≤ d^2) : a^4 + b^4 + c^4 + d^4 ≥ d^5 := by
  intros
  clear habc
  have hcubes : d^3 ≤ d^2 := by nlinarith [pow_nonneg ha 3, pow_nonneg hb 3, pow_nonneg hc 3]
  have hdle : d ≤ 1 := by
    by_contra hn
    have hdgt : 1 < d := lt_of_not_ge hn
    have hpos : 0 < d^2 * (d - 1) := mul_pos (pow_pos (by linarith) 2) (by linarith)
    nlinarith
  calc
    d^5 = d^4 * d := by ring
    _ ≤ d^4 * 1 := mul_le_mul_of_nonneg_left hdle (pow_nonneg hd 4)
    _ ≤ a^4 + b^4 + c^4 + d^4 := by nlinarith [pow_nonneg ha 4, pow_nonneg hb 4, pow_nonneg hc 4]
