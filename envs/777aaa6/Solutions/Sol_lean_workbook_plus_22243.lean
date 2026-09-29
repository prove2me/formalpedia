-- Prove2me | solution 1 for lean_workbook_plus_22243
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:32:26.75203+00:00
-- url     : https://prove2.me/submissions/cc2f17be-0949-408c-a572-e2b7b1222a48

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (h : 0 < √2) : (Real.sqrt ((17 - √2) * (17 + √2)) - 10) * (Real.sqrt ((17 - √2) * (17 + √2)) + 10) = 187 := by
  intros
  grind
