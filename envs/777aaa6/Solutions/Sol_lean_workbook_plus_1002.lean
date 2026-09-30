-- Prove2me | solution 1 for lean_workbook_plus_1002
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:59:59.572557+00:00
-- url     : https://prove2.me/submissions/8e0fbfcc-5bc2-43a1-8a71-c31baa1cccd1

import Mathlib
set_option autoImplicit false

theorem solution (a b c d : ℝ) (hb : 0 < b) (hd : 0 < d) (h : a / b < c / d) : a / b < (a + c) / (b + d) ∧ (a + c) / (b + d) < c / d   := by
  have hc : a * d < c * b := (div_lt_div_iff₀ hb hd).mp h
  constructor
  · apply (div_lt_div_iff₀ hb (add_pos hb hd)).mpr
    nlinarith only [hc]
  · apply (div_lt_div_iff₀ (add_pos hb hd) hd).mpr
    nlinarith only [hc]

#print axioms solution
