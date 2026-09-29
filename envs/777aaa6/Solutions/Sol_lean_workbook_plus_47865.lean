-- Prove2me | solution 1 for lean_workbook_plus_47865
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:04:36.213461+00:00
-- url     : https://prove2.me/submissions/567b1f83-da9b-4642-9e4b-d17eb5ec4f53

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ (x : ZMod 11), x ^ 2 = 0 ∨ x ^ 2 = 1 ∨ x ^ 2 = 4 ∨ x ^ 2 = 9 ∨ x ^ 2 = 5 ∨ x ^ 2 = 3 := by
  decide
