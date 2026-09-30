-- Prove2me | solution 1 for lean_workbook_plus_29447
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:40:39.911039+00:00
-- url     : https://prove2.me/submissions/c6423849-6155-4ad7-b206-80b7da25791e

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) (hx : 0 < x ∧ x ≤ 1) :
  x + (1 / x ^ 2) ≥ 2 := by
  obtain ⟨h0, h1⟩ := hx
  have hx2 : 0 < x ^ 2 := by positivity
  rw [ge_iff_le, ← sub_nonneg]
  have e : x + 1 / x ^ 2 - 2 = (x - 1) * (x ^ 2 - x - 1) / x ^ 2 := by
    field_simp
    ring
  rw [e]
  apply div_nonneg _ hx2.le
  exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by nlinarith)
