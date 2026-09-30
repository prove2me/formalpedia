-- Prove2me | solution 1 for lean_workbook_plus_9621
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:50:56.3418+00:00
-- url     : https://prove2.me/submissions/38c56c2a-4ab0-4d42-9abd-b4153490c942

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) : a + b + c ≤ 2 + a * b * c   := by
  have hab : a * b ≤ 1 := by
    calc
      a * b ≤ 1 * b := mul_le_mul_of_nonneg_right ha.2 hb.1
      _ ≤ 1 := by simpa using hb.2
  have hp : 0 ≤ (1 - a) * (1 - b) :=
    mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hb.2)
  have hq : 0 ≤ (1 - a * b) * (1 - c) :=
    mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hc.2)
  nlinarith only [hp, hq]

#print axioms solution
