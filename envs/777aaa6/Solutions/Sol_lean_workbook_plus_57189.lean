-- Prove2me | solution 1 for lean_workbook_plus_57189
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:24:10.705201+00:00
-- url     : https://prove2.me/submissions/c76f2c8a-6772-48ce-9b1e-a7f69631abfd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h₁ : a + b = 2) : b = 2 - a := by
  (intros; linarith)
