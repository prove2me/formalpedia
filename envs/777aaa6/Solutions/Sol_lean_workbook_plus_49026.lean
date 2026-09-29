-- Prove2me | solution 1 for lean_workbook_plus_49026
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:37:14.707208+00:00
-- url     : https://prove2.me/submissions/ed5badc3-0b6c-4012-b543-d318a7d5a89f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c : ℝ} : (2 * a ^ 2 - b ^ 2 - c ^ 2) ^ 2 ≥ 0 := by
  (intros; positivity)
