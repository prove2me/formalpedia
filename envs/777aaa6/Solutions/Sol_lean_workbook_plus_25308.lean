-- Prove2me | solution 1 for lean_workbook_plus_25308
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:26:46.739755+00:00
-- url     : https://prove2.me/submissions/f9cdaddb-c06c-409d-b8a7-6bfbd135c79c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a + b - c) ^ 2 ≥ 0 := by
  (intros; positivity)
