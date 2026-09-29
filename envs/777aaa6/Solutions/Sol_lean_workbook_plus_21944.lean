-- Prove2me | solution 1 for lean_workbook_plus_21944
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:45:13.988502+00:00
-- url     : https://prove2.me/submissions/8dcee592-c1a6-468d-8caf-3a6682fe78c2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a : ℝ, ∃ l : ℝ, ∑' n : ℕ, (a ^ n / n.factorial) = l := by
  norm_num
