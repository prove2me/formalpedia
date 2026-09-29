-- Prove2me | solution 1 for lean_workbook_plus_24744
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:27:55.269451+00:00
-- url     : https://prove2.me/submissions/751a07aa-ce8f-4f7a-bc1f-35a781a53dac

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x : ℝ, ∀ n : ℤ, (Int.ceil (x + n) = Int.ceil x + n) := by
  norm_num
