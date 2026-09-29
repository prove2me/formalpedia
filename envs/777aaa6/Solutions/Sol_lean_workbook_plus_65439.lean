-- Prove2me | solution 1 for lean_workbook_plus_65439
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:50:26.040495+00:00
-- url     : https://prove2.me/submissions/a647d90c-cae7-405c-9141-fe99d7bc91e8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (k : ℝ) (h₁ : 0 < k) (h₂ : 2 * (3 - Real.sqrt 5) ≤ k) (h₃ : k ≤ 2 * (3 + Real.sqrt 5)) : 2 * (3 - Real.sqrt 5) ≤ k ∧ k ≤ 2 * (3 + Real.sqrt 5) := by
  (intros; simp_all)
