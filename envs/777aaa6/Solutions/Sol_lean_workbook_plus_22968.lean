-- Prove2me | solution 1 for lean_workbook_plus_22968
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:24:23.483775+00:00
-- url     : https://prove2.me/submissions/295b7977-a194-46c0-a047-25ab92869048

import Mathlib.Analysis.Complex.Basic

theorem solution {r s R : ℝ} (h₁ : r ≥ 0 ∧ s ≥ 0 ∧ R ≥ 0) (h₂ : r ≤ s) (h₃ : s ≤ R + r) (h₄ : R ≤ s + r) : 16 * r ^ 2 * s ^ 2 * (3 * r ^ 2 - s ^ 2 + 4 * R * r + 4 * R ^ 2) ≥ 0 := by
  obtain ⟨hr, hs, hR⟩ := h₁
  apply mul_nonneg
  · positivity
  · nlinarith [mul_le_mul h₃ h₃ hs (by linarith), sq_nonneg r, sq_nonneg R, mul_nonneg hR hr]
