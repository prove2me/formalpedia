-- Prove2me | solution 1 for lean_workbook_plus_5034
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:16:23.999673+00:00
-- url     : https://prove2.me/submissions/411a37ff-6211-4dbc-9e62-ca159eedd430

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h₁ : a + b = 24) (h₂ : a = 3 * b / 5) : b = 15 := by
  (intros; linarith)
