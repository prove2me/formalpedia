-- Prove2me | solution 1 for lean_workbook_plus_14910
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:31:16.239396+00:00
-- url     : https://prove2.me/submissions/422c6366-e351-450c-9ff2-9916c8f910c2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (F_X1 F_X2 : ℝ → ℝ) (t : ℝ) (h1 : 0 ≤ F_X1 t ∧ 0 ≤ F_X2 t) (h2 : F_X1 t ≤ F_X2 t) (h3 : 1 ≥ 1 - F_X1 t ∧ 1 ≥ 1 - F_X2 t) (h4 : 1 - F_X1 t ≥ 1 - F_X2 t) : 0 ≤ F_X1 t ∧ 0 ≤ F_X2 t ∧ F_X1 t ≤ F_X2 t ∧ 1 ≥ 1 - F_X1 t ∧ 1 ≥ 1 - F_X2 t ∧ 1 - F_X1 t ≥ 1 - F_X2 t := by
  (intros; simp_all)
