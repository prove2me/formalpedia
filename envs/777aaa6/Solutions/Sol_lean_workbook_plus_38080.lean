-- Prove2me | solution 1 for lean_workbook_plus_38080
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:52:49.8398+00:00
-- url     : https://prove2.me/submissions/36e5b08b-05ec-4b2c-8793-9ccf61c8060e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (k c : ℝ)
  (h₀ : 5 * k ≤ c)
  (h₁ : c ≤ 6 * k)
  (h₂ : 6 * k - 10 ≤ c)
  (h₃ : c ≤ 5 * k + 7) :
  max (5 * k) (6 * k - 10) ≤ c ∧ c ≤ min (6 * k) (5 * k + 7) := by
  (intros; simp_all)
