-- Prove2me | solution 1 for lean_workbook_plus_7988
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:50:55.455286+00:00
-- url     : https://prove2.me/submissions/c2b6bd1f-1c27-47fb-baed-b94314e5456e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c d : ℤ} : (a + b + c + d)^4 + (a + b - c - d)^4 + (a - b + c - d)^4 + (a - b - c + d)^4 - (a + b + c - d)^4 - (a + b - c + d)^4 - (a - b + c + d)^4 - ( - a + b + c + d)^4 = 192 * a * b * c * d := by
  (intros; linarith)
