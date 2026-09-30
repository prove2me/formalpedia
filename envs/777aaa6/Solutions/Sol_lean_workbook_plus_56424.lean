-- Prove2me | solution 1 for lean_workbook_plus_56424
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:13:49.047225+00:00
-- url     : https://prove2.me/submissions/26918c13-d630-4699-8d81-437b7dc4b8e7

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 ≥ (a + b + c) / (a * b * c)   := by
  have he : (a + b + c) / (a * b * c) =
      (1 / a) * (1 / b) + (1 / b) * (1 / c) + (1 / c) * (1 / a) := by
    field_simp [ha, hb, hc]
    <;> ring
  have hs (x : ℝ) : 1 / x ^ 2 = (1 / x) ^ 2 := by simp [div_pow]
  rw [he, hs a, hs b, hs c]
  nlinarith [sq_nonneg (1 / a - 1 / b), sq_nonneg (1 / b - 1 / c),
    sq_nonneg (1 / c - 1 / a)]

#print axioms solution
