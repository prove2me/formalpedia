-- Prove2me | solution 1 for lean_workbook_plus_1582
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:24:10.675195+00:00
-- url     : https://prove2.me/submissions/3dc96a7e-7e52-4ef5-8a08-525c3d1fb93f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) : 1 + x^2 ≤ (1 + x)^2 := by
  (intros; linarith)
