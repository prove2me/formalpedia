-- Prove2me | solution 1 for lean_workbook_plus_81363
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:13:49.427421+00:00
-- url     : https://prove2.me/submissions/89fc379a-d53e-41f0-ac22-0fd6a0aa5d71

import Mathlib

theorem solution (a b c d : ℝ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (habc : (a - 1) * (b - 1) * (c - 1) * (d - 1) = 1) :
    1 / a + 1 / b + 1 / c + 1 / d ≤ 2 := by
  have bound (u : ℝ) (hu : 2 ≤ u) : 1 / u ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (by linarith : 0 < u)).2
    linarith
  linarith [bound a ha, bound b hb, bound c hc, bound d hd]
