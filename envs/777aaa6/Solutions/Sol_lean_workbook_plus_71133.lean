-- Prove2me | solution 1 for lean_workbook_plus_71133
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:17:59.004323+00:00
-- url     : https://prove2.me/submissions/eada3aad-5a49-444a-9e76-47320c974a90

import Mathlib

theorem solution (a b : ℝ) (hab : a ≥ 1 ∧ b ≥ 1) :
    a^5 + b^5 ≥ (a + b) * a^2 * b^2 := by
  have ha : 0 ≤ a := by linarith [hab.1]
  have hb : 0 ≤ b := by linarith [hab.2]
  have h : 0 ≤ (a - b)^2 * (a + b) * (a^2 + a*b + b^2) := by positivity
  nlinarith

#print axioms solution
