-- Prove2me | solution 1 for lean_workbook_plus_27394
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:18:38.203244+00:00
-- url     : https://prove2.me/submissions/079f0d18-1c7e-4795-aff3-de5894bea855

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2 := by
  (intros; ring)
