-- Prove2me | solution 1 for lean_workbook_plus_46162
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:15:16.191911+00:00
-- url     : https://prove2.me/submissions/c87f5e96-97c8-4cba-a4b8-5bc46d90cfbf

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x = 10^302) : x^2 / x^2 = 1 := by
  (intros; simp_all)
