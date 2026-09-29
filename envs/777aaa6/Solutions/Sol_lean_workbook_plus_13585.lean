-- Prove2me | solution 1 for lean_workbook_plus_13585
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:23:00.958725+00:00
-- url     : https://prove2.me/submissions/ed4a5485-988d-4adf-a9d0-0ed01689cea4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c : ℝ} : (a - 2 * b + c) ^ 2 ≥ 0 := by
  (intros; positivity)
