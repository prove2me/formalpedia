-- Prove2me | solution 1 for lean_workbook_plus_18118
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:56:11.569741+00:00
-- url     : https://prove2.me/submissions/c1329496-1b82-497e-9c3a-7a5de8d7cc61

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf : f = fun x => x^3 + x + 1) : ∃ g, g = f⁻¹ := by
  norm_num
