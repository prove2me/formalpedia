-- Prove2me | solution 1 for lean_workbook_plus_65393
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:06:04.334383+00:00
-- url     : https://prove2.me/submissions/63e4388f-f3c8-4b73-94bf-787217759005

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c : ℝ} :  (a^2 - b^2)^2 + (b^2 - c^2)^2 + (c^2 - a^2)^2 ≥ 0 := by
  (intros; positivity)
