-- Prove2me | solution 1 for lean_workbook_plus_24391
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:41:05.772315+00:00
-- url     : https://prove2.me/submissions/8c16026f-fbf2-405c-be69-c7e3891a4269

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ x y : ℝ, 0 ≤ x ∧ x ≤ y ∧ y ≤ 1 → 1 / 4 ≥ y * x ^ 2 - x * y ^ 2 := by
  intro x y ⟨hx, hxy, hy⟩
  have hxy0 : 0 ≤ x * y := mul_nonneg hx (hx.trans hxy)
  nlinarith [mul_nonneg hxy0 (sub_nonneg.mpr hxy)]
