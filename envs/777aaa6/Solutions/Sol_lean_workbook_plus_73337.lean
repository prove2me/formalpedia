-- Prove2me | solution 1 for lean_workbook_plus_73337
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:04:15.982927+00:00
-- url     : https://prove2.me/submissions/7f3152bc-6862-4fb9-a996-6f1ca481f1a5

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    2 * (a ^ 3 + b ^ 3 + c ^ 3) ≥
      a ^ 2 * (b + c) + b ^ 2 * (a + c) + c ^ 2 * (a + b) := by
  nlinarith [mul_nonneg (sq_nonneg (a - b)) (add_nonneg ha hb),
    mul_nonneg (sq_nonneg (a - c)) (add_nonneg ha hc),
    mul_nonneg (sq_nonneg (b - c)) (add_nonneg hb hc)]

#check @solution
#print axioms solution
