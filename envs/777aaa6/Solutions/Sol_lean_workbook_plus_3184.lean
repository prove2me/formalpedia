-- Prove2me | solution 1 for lean_workbook_plus_3184
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:40:40.884479+00:00
-- url     : https://prove2.me/submissions/5f524cf6-ac71-4ad5-a0db-ef8d5d38392a

import Mathlib.Analysis.Complex.Basic

theorem solution {x y z : ℝ} : 2*y*(1 + x^2 + y^2 + z^2)*(x^3 + z^3 + x*y*z + x*z) ≤ (y*(1 + x^2 + y^2 + z^2) + 2*(x^3 + z^3 + x*y*z + x*z))^2 / 4 := by
  nlinarith [sq_nonneg (y*(1 + x^2 + y^2 + z^2) - 2*(x^3 + z^3 + x*y*z + x*z))]
