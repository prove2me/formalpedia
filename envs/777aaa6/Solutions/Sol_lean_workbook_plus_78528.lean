-- Prove2me | solution 1 for lean_workbook_plus_78528
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:14:11.284316+00:00
-- url     : https://prove2.me/submissions/a595fbe2-9cac-498d-9042-4465b7f8a7ca

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : ∀ x y z : ℝ, 5 * (x ^ 2 + y ^ 2 + z ^ 2) ≥
    6 * x * y - 8 * x * z + 8 * y * z := by
  intro x y z
  nlinarith [sq_nonneg (x + y), sq_nonneg (2 * x - 2 * y + 2 * z), sq_nonneg z]

#print axioms solution
