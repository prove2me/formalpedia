-- Prove2me | solution 1 for lean_workbook_plus_73686
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:11:39.037698+00:00
-- url     : https://prove2.me/submissions/71de7e0a-0873-4ba6-8964-a508a0c46cd6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) :
    (a ^ 4 + b ^ 4 + c ^ 4) / 3 ≥ (a + b + c) ^ 4 / 81 := by
  have hs : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    nlinarith only [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have hq : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≤ 3 * (a ^ 4 + b ^ 4 + c ^ 4) := by
    nlinarith only [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2),
      sq_nonneg (c ^ 2 - a ^ 2)]
  have hp : 0 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) + (a + b + c) ^ 2 := by positivity
  have hm := mul_nonneg (sub_nonneg.mpr hs) hp
  nlinarith only [hq, hm]
