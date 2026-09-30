-- Prove2me | solution 1 for lean_workbook_plus_81282
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:23:39.432288+00:00
-- url     : https://prove2.me/submissions/77743a25-38f8-4676-8f0f-86fab4bfdc9a

import Mathlib.Analysis.Complex.Basic

theorem solution (x y : ℕ) (hx : 100 ≤ x ∧ x ≤ 1000) (hy : 100 ≤ y ∧ y ≤ 1000) (h : 1000 * x + (1000 - x) = y ^ 2) : 999 * (x + 1) ≡ 0 [ZMOD 27 * 37] := by
  rw [Int.modEq_zero_iff_dvd]
  exact ⟨(x : ℤ) + 1, by ring⟩
