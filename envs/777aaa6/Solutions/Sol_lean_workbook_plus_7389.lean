-- Prove2me | solution 1 for lean_workbook_plus_7389
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:05:53.991449+00:00
-- url     : https://prove2.me/submissions/f32d2f26-308c-44d3-8019-a7162a4b562e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) : (∃ x, 4*x^2 - 40 * Int.floor x + 51 = 0) ↔ ∃ x, 4*x^2 - 40 * Int.ceil x + 51 = 0 := by
  norm_num
