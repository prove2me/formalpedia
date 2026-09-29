-- Prove2me | solution 1 for lean_workbook_plus_23294
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:54:58.705945+00:00
-- url     : https://prove2.me/submissions/53aff5a1-82e2-415b-9ea1-f0168937e4f8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℕ) (hn : 2 ≤ n) (a_n : ℝ) (ha_n : a_n = (1 + n + n^2) / (Real.sqrt (1 + n^2 + n^6))) : ∃ l, ∑' n : ℕ, a_n = l := by
  norm_num
