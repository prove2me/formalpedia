-- Prove2me | solution 1 for lean_workbook_plus_19303
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:43:56.755214+00:00
-- url     : https://prove2.me/submissions/ab74a636-afee-431a-92b6-a5bd3faa9580

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℤ) : (x + y) * (y + z) * (z + x) = (x + y + z) * (x*y + y*z + z*x) - x*y*z := by
  (intros; linarith)
