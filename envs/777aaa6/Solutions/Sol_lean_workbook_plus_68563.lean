-- Prove2me | solution 1 for lean_workbook_plus_68563
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:12:21.433933+00:00
-- url     : https://prove2.me/submissions/dfe28c1d-47af-4a4a-aead-b39c282879fe

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) :
  (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a) := by
  (intros; linarith)
