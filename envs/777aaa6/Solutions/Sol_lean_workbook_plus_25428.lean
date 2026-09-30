-- Prove2me | solution 1 for lean_workbook_plus_25428
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:43:28.553731+00:00
-- url     : https://prove2.me/submissions/010625ba-4dfe-47c7-9b16-0d1dc4b29089

import Mathlib.Analysis.Complex.Basic

theorem solution (a : ℤ) : gcd (2*a + 1) (9*a + 4) = 1 := by
  rw [← Int.coe_gcd]
  have h : IsCoprime (2*a + 1) (9*a + 4) := ⟨9, -2, by ring⟩
  rw [Int.isCoprime_iff_gcd_eq_one] at h
  rw [h]
  rfl
