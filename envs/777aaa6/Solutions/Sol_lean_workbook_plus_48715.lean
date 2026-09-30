-- Prove2me | solution 1 for lean_workbook_plus_48715
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:45:46.973979+00:00
-- url     : https://prove2.me/submissions/74a54e30-ce73-45cf-be6f-9273df4da80e

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) (h : x + y + z = 0) : (x^2 + y^2 + z^2) / 2 * (x^3 + y^3 + z^3) / 3 = (x^5 + y^5 + z^5) / 5 := by
  have hz : z = -x - y := by linarith
  subst hz
  ring
