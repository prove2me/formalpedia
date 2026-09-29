-- Prove2me | solution 1 for lean_workbook_plus_11790
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:48:41.992167+00:00
-- url     : https://prove2.me/submissions/1b282d4a-7472-4af1-b482-617bb6a00a32

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x + y + z = 7) (hy : x*y + y*z + z*x = 10) (hz : x*y*z = 5) : (2 - x) * (2 - y) * (2 - z) = -5 := by
  (intros; linarith)
