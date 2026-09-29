-- Prove2me | solution 1 for lean_workbook_plus_30902
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:54:25.05675+00:00
-- url     : https://prove2.me/submissions/4c9af106-c8b1-42f3-a576-2fc5e213a094

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a b c : ℝ,  -a+b+c<0 ∧ a-b+c<0 → c<0 := by
  (intros; linarith)
