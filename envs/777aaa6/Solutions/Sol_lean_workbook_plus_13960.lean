-- Prove2me | solution 1 for lean_workbook_plus_13960
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:30:08.04435+00:00
-- url     : https://prove2.me/submissions/2531e9bb-ba57-4f21-ae6c-702b22dd5787

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (m x y z : ℝ) (hx : x = (m + 9) / 2) (hy : y = (2 * m + 15) / 2) (hz : z = (3 * m + 18) / 2) : (x + y + z) / 3 = m + 7 := by
  (intros; linarith)
