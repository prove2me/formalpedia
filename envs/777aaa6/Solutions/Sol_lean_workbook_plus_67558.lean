-- Prove2me | solution 1 for lean_workbook_plus_67558
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:10:49.404552+00:00
-- url     : https://prove2.me/submissions/dff6feed-6298-4f35-b9b3-58f314b8e4c8

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b : ℝ) (h1 : 0 < a ∧ 0 < b) (h2 : a ≤ 2 * b)
    (h3 : 2 * b ≤ 4 * a) :
    4 * a * b ≤ 2 * (a ^ 2 + b ^ 2) ∧ 2 * (a ^ 2 + b ^ 2) ≤ 5 * a * b := by
  have hp : 0 ≤ (2 * b - a) * (2 * a - b) :=
    mul_nonneg (by linarith) (by linarith)
  constructor <;> nlinarith [sq_nonneg (a - b)]

#print axioms solution
