-- Prove2me | solution 1 for lean_workbook_plus_29421
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:42:04.018729+00:00
-- url     : https://prove2.me/submissions/75567df7-372d-4b3f-b9ad-43e81331c857

import Mathlib
set_option autoImplicit false

theorem solution (a b c d : ℝ) (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) (hd : d ∈ Set.Icc 0 1) : a * (1 - d) + b * (1 - a) + c * (1 - b) + d * (1 - c) ≤ 2   := by
  by_cases hs : a + c ≤ 1
  · have hp : 0 ≤ (2 - (b + d)) * (1 - (a + c)) :=
      mul_nonneg (by linarith only [hb.2, hd.2]) (by linarith only [hs])
    nlinarith only [hp, ha.1, hc.1]
  · have hp : 0 ≤ (b + d) * (a + c - 1) :=
      mul_nonneg (by linarith only [hb.1, hd.1]) (by linarith only [hs])
    nlinarith only [hp, ha.2, hc.2]

#print axioms solution
