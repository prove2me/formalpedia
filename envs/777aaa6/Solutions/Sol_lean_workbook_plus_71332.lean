-- Prove2me | solution 1 for lean_workbook_plus_71332
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:34:55.629218+00:00
-- url     : https://prove2.me/submissions/4b859436-22a6-4360-a359-b109228e9d04

import Mathlib

theorem solution (m k : ℕ) : m ≥ 3 ∧ k > 1 → k^(m+1) ≥ 1+k^2 := by
  rintro ⟨hm, hk⟩
  have hk2 : 2 ≤ k := by omega
  have hp : k^3 ≤ k^(m+1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hmul : 2 * k^2 ≤ k * k^2 := Nat.mul_le_mul_right _ hk2
  nlinarith

#print axioms solution
