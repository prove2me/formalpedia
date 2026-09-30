-- Prove2me | solution 1 for lean_workbook_plus_77000
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:05:20.767974+00:00
-- url     : https://prove2.me/submissions/a04daf89-546f-432a-b6bf-6cbcb4a94f50

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution (x : ℝ) (hx : 0 < x) :
    (x^3 + 1 + 1) / 3 ≥ x ∧ (x^3 + x^3 + 1) / 3 ≥ x^2 := by
  have h1 : 0 ≤ (x - 1)^2 * (x + 2) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have h2 : 0 ≤ (x - 1)^2 * (2*x + 1) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  constructor <;> nlinarith
