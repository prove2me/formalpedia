-- Prove2me | solution 1 for lean_workbook_plus_10941
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:16:51.021772+00:00
-- url     : https://prove2.me/submissions/ea173cb2-07db-46ad-a0b7-a91feb8fd4a1

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) (h : x*y*z = -2) : (x + y + z)^3 = x^3 + y^3 + z^3 + 6*x*y*z + 3*(x^2*y + x^2*z + y^2*x + y^2*z + z^2*x + z^2*y) := by
  ring
