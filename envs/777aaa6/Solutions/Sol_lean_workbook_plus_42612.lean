-- Prove2me | solution 1 for lean_workbook_plus_42612
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:40:07.955248+00:00
-- url     : https://prove2.me/submissions/52c08cf7-6bc2-4f5f-9b0c-224d15d3e24b

import Mathlib.Analysis.Complex.Basic

theorem solution  (n : ℕ)
  (h₀ : 0 < n) :
  ((Nat.gcd n n) / n * (n.choose n) : ℚ).den = 1 := by
  have hn : (n : ℚ) ≠ 0 := by positivity
  rw [Nat.gcd_self, Nat.choose_self]
  push_cast
  rw [div_self hn, one_mul]
  rfl
