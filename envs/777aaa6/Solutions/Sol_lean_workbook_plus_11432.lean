-- Prove2me | solution 1 for lean_workbook_plus_11432
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:56:17.171714+00:00
-- url     : https://prove2.me/submissions/757555d5-f5e1-4347-bb89-22292c8d9bbd

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : Nat.lcm a b = 30)
  (h₂ : Nat.gcd a b = 2) :
  a * b = 60 := by
  rw [← Nat.gcd_mul_lcm a b, h₁, h₂]
