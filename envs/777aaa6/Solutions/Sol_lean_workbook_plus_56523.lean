-- Prove2me | solution 1 for lean_workbook_plus_56523
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:23:19.725035+00:00
-- url     : https://prove2.me/submissions/e7f9159b-d287-4788-9bcc-11a174895b66

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z α β s : ℝ) (hx : x + y + z = α + β) (hy : x*y + y*z + z*x = α*β) (hz : x*y*z = s) : x*y*z = s := by
  (intros; simp_all)
