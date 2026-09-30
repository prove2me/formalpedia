-- Prove2me | solution 1 for lean_workbook_plus_60373
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:25:06.455031+00:00
-- url     : https://prove2.me/submissions/6c26ba4d-9e3d-4844-9db6-eeb5fdee6488

import Mathlib.Analysis.Complex.Basic

theorem solution (m n : ℤ) (h₁ : m ∣ n^2 + 1) (h₂ : n ∣ m^2 + 1) : ∃ m n, (m ∣ n^2 + 1 ∧ n ∣ m^2 + 1) ∧ (m > n) := by
  exact ⟨2, 1, ⟨by norm_num, by norm_num⟩, by norm_num⟩
