-- Prove2me | solution 1 for lean_workbook_plus_12649
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:32:35.68298+00:00
-- url     : https://prove2.me/submissions/17fe069f-7782-4eaf-b907-fbd5aa22b1aa

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : x * y ^ 2 + y * z ^ 2 + z * x ^ 2 + x * y * z ≥ 0 := by
  (intros; positivity)
