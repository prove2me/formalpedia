-- Prove2me | solution 1 for lean_workbook_plus_49745
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:40:38.284931+00:00
-- url     : https://prove2.me/submissions/c4fc4d86-5372-4ba1-8bb3-9f139ea3d1b9

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℤ) : ∃ x y : ℤ, gcd a b = x * a + y * b := by
  refine ⟨Int.gcdA a b, Int.gcdB a b, ?_⟩
  rw [← Int.coe_gcd, Int.gcd_eq_gcd_ab]
  ring
