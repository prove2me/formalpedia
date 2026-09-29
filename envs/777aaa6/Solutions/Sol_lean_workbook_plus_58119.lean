-- Prove2me | solution 1 for lean_workbook_plus_58119
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:45:31.708087+00:00
-- url     : https://prove2.me/submissions/71165805-804d-4fef-8a7d-74efe62f0a3e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (p s : ℝ) (hp: p = x*y) (hs: s = x+y) : (s^2 - 6 * p)^2 ≥ 0 := by
  (intros; positivity)
