-- Prove2me | solution 1 for lean_workbook_plus_78132
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:54:18.573278+00:00
-- url     : https://prove2.me/submissions/28453f2c-987a-41ad-8a6d-b07b4a795184

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

private theorem reciprocal_bound (t : ℝ) (h : 3/2 ≤ t) : 1/t ≤ 2/3 := by
  have ht : 0 < t := by linarith only [h]
  apply (div_le_iff₀ ht).2
  linarith only [h]

theorem solution (a b c : ℝ) (ha : 3 / 2 ≤ a) (hb : 3 / 2 ≤ b)
    (hc : 3 / 2 ≤ c) :
    a + b + c ≥ 3 / 2 * (1 / a + 1 / b + 1 / c + 1) := by
  linarith only [ha, hb, hc, reciprocal_bound a ha,
    reciprocal_bound b hb, reciprocal_bound c hc]
