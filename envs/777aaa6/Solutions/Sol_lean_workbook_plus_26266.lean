-- Prove2me | solution 1 for lean_workbook_plus_26266
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:26:10.665491+00:00
-- url     : https://prove2.me/submissions/7558cd7c-de35-477f-a47a-3b6947773fb1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x y z : ℝ, x / (x ^ 2 + 1) + y / (y ^ 2 + 1) + z / (z ^ 2 + 1) = 1 / 2 * ((x + 1) ^ 2 / (x ^ 2 + 1) + (y + 1) ^ 2 / (y ^ 2 + 1) + (z + 1) ^ 2 / (z ^ 2 + 1)) - 3 / 2 := by
  (intros; field_simp; ring)
