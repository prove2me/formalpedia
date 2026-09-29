-- Prove2me | solution 1 for lean_workbook_plus_63193
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:17:36.940836+00:00
-- url     : https://prove2.me/submissions/4a7b613f-c3f3-43a9-bb5c-01820c546638

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (b c : ℝ) (h : b + c ≥ 1 + b * c) :
  2 * (b + c) ≥ (b + 1) * (c + 1) := by
  (intros; linarith)
