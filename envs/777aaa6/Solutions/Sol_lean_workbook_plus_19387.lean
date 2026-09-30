-- Prove2me | solution 1 for lean_workbook_plus_19387
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:25:12.000614+00:00
-- url     : https://prove2.me/submissions/2d9a4cb4-afe8-44e2-913d-71544f44b9bc

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) (h : n % 4 = 0) : ∃ a b, a % 2 = 0 ∧ b % 2 = 0 ∧ n = a * b := by
  exact ⟨2, n / 2, by norm_num, by omega, by omega⟩
