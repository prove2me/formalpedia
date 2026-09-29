-- Prove2me | solution 1 for lean_workbook_plus_32075
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:43:49.061439+00:00
-- url     : https://prove2.me/submissions/7699b3a9-0fcc-4a3e-9dd7-3404227029e6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ)
  (h₀ : 0 ≤ x ∧ 0 ≤ y)
  (h₁ : x ≥ y) :
  x^3 + y^3 ≥ (x^2 + y^2) * (x + y) / 2 ∧ (x^2 + y^2) * (x + y) / 2 ≥ (x + y)^3 / 4 := by
  (intros; constructor <;> nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
