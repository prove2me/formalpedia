-- Prove2me | solution 1 for lean_workbook_plus_12421
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:42:14.461036+00:00
-- url     : https://prove2.me/submissions/30ac3fa6-a3c4-4549-a443-2ac01cfb3db5

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) (hx: 0 ≤ x ∧ x ≤ 1) : 0 ≤ x - x^2 ∧ x - x^2 ≤ 1/4 := by
  obtain ⟨h0, h1⟩ := hx
  constructor
  · nlinarith [mul_nonneg h0 (sub_nonneg.2 h1)]
  · nlinarith [sq_nonneg (x - 1/2)]
