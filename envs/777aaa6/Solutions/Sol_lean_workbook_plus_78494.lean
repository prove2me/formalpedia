-- Prove2me | solution 1 for lean_workbook_plus_78494
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:25:42.3882+00:00
-- url     : https://prove2.me/submissions/c56a664c-a88e-4222-bd51-a4a0f4ce169e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∃ (v : ℕ → ℝ), ∀ n, Odd n → v n = 1 ∧ Even n → v n = 1 / n := by
  (intros; simp_all)
