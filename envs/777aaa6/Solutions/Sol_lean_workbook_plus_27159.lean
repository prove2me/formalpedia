-- Prove2me | solution 1 for lean_workbook_plus_27159
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:15:00.903647+00:00
-- url     : https://prove2.me/submissions/bbc08b3c-c545-4adf-a9c6-72dae65ade8e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ n : ℝ, n^4-6*n^3+14*n^2-16*n+8 ≥ 0 ↔ (n^2-2*n+2)*(n-2)^2 ≥ 0 := by
  (intros; field_simp; ring)
