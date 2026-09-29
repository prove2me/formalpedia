-- Prove2me | solution 1 for lean_workbook_plus_33666
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:15:16.648219+00:00
-- url     : https://prove2.me/submissions/f290cead-97b5-45b1-9a8a-83cdc0c2fc9c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℕ → ℝ) (ha : a 1 = 1 / Real.sqrt 2) (hb : b 1 = 1 / Real.sqrt 2) (ha2 : a 2 = 1) (hb2 : b 2 = 1) : ∃ (f g : ℕ → ℝ), a = f ∧ b = g := by
  norm_num
