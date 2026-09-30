-- Prove2me | solution 1 for lean_workbook_plus_75568
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:00:42.369676+00:00
-- url     : https://prove2.me/submissions/bd9946dc-98f1-4aa0-b20e-882cb0bd5ffb

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

private lemma reciprocal_pair (a : ℝ) (ha : 0 < a) : 2 ≤ a + 1 / a := by
  have h := div_nonneg (sq_nonneg (a - 1)) ha.le
  have hid : (a - 1) ^ 2 / a = a + 1 / a - 2 := by
    field_simp [ne_of_gt ha] <;> ring
  rw [hid] at h
  linarith

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a + b + c ≥ 1/a + 1/b + 1/c → a^3 + b^3 + c^3 ≥ a + b + c := by
  intro hsum
  have hS : 3 ≤ a + b + c := by
    linarith [reciprocal_pair a ha, reciprocal_pair b hb, reciprocal_pair c hc]
  have h1 := mul_nonneg (sq_nonneg (a - 1)) (show 0 ≤ a + 2 by positivity)
  have h2 := mul_nonneg (sq_nonneg (b - 1)) (show 0 ≤ b + 2 by positivity)
  have h3 := mul_nonneg (sq_nonneg (c - 1)) (show 0 ≤ c + 2 by positivity)
  nlinarith

#print axioms solution
