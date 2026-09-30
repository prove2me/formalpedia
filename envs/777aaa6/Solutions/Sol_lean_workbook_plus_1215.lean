-- Prove2me | solution 1 for lean_workbook_plus_1215
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:00:29.519496+00:00
-- url     : https://prove2.me/submissions/58fd5535-a844-483c-a792-6b9149119b7e

import Mathlib
set_option autoImplicit false

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (c + d) * (1 / (a + d) + 1 / (b + c)) ≥ 4 * (c + d) / (a + b + c + d)   := by
  have hu : 0 < a + d := add_pos ha hd
  have hv : 0 < b + c := add_pos hb hc
  have hs : 0 < a + b + c + d := by positivity
  have hr : 4 / (a + b + c + d) ≤ 1 / (a + d) + 1 / (b + c) := by
    apply (div_le_iff₀ hs).mpr
    apply (mul_le_mul_iff_right₀ (mul_pos hu hv)).mp
    have he : ((1 / (a + d) + 1 / (b + c)) * (a + b + c + d) - 4) *
        ((a + d) * (b + c)) = (a + d - (b + c)) ^ 2 := by
      field_simp [ne_of_gt hu, ne_of_gt hv]
      ring
    nlinarith only [he, sq_nonneg (a + d - (b + c))]
  have hm := mul_le_mul_of_nonneg_left hr (le_of_lt (add_pos hc hd))
  calc
    4 * (c + d) / (a + b + c + d) = (c + d) * (4 / (a + b + c + d)) := by ring
    _ ≤ (c + d) * (1 / (a + d) + 1 / (b + c)) := hm

#print axioms solution
