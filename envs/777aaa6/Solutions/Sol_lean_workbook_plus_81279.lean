-- Prove2me | solution 1 for lean_workbook_plus_81279
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:37:25.862525+00:00
-- url     : https://prove2.me/submissions/883835f6-8c79-4173-941a-4a2cb6b0dca9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (s b r : ℝ) : s = 111 / 20 * r ∧ s = 3 * (s - b) → 2 * s = 3 * b := by
  (intros; linarith)
