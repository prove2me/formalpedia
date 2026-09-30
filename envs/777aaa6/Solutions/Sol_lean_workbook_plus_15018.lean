-- Prove2me | solution 1 for lean_workbook_plus_15018
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:07:22.259759+00:00
-- url     : https://prove2.me/submissions/58f4382f-d296-48a1-8dfb-cc98f9a017ef

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / (√a + √((a + b) * (a + c))) ≤ 1 / 9 * (1 / √a + 4 / √((a + b) * (a + c))) := by
  have key : ∀ u v : ℝ, 0 < u → 0 < v → 1 / (u + v) ≤ 1 / 9 * (1 / u + 4 / v) := by
    intro u v hu hv
    have huv : 0 < u + v := by positivity
    rw [div_add_div _ _ hu.ne' hv.ne', ← mul_div_assoc, div_le_div_iff₀ huv (by positivity)]
    nlinarith [sq_nonneg (v - 2 * u), mul_pos hu hv]
  exact key _ _ (Real.sqrt_pos.mpr ha) (Real.sqrt_pos.mpr (by positivity))
