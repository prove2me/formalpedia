-- Prove2me | solution 1 for lean_workbook_plus_66548
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:47:56.239757+00:00
-- url     : https://prove2.me/submissions/2e74ea20-ef6d-4e89-a365-8041b9b7e963

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (u v w : ℝ) :
  (u - v) ^ 2 * (u - w) ^ 2 * (v - w) ^ 2 ≥ 0 := by
  (intros; positivity)
