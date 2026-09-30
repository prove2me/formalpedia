-- Prove2me | solution 1 for lean_workbook_plus_16942
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:59:30.024473+00:00
-- url     : https://prove2.me/submissions/44551765-c4ef-4c44-9c18-96b6a45442e2

import Mathlib.Analysis.Complex.Basic

theorem solution (a : ℤ) : gcd a (a + 1) = 1 := by
  rw [← Int.coe_gcd]
  have hc : IsCoprime a (a + 1) := ⟨-1, 1, by ring⟩
  rw [Int.isCoprime_iff_gcd_eq_one] at hc
  rw [hc]
  norm_num
