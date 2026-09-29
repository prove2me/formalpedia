-- Prove2me | solution 1 for lean_workbook_plus_44680
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:01:55.675106+00:00
-- url     : https://prove2.me/submissions/da979531-5869-4e2f-8049-1d5976bfc7d2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℂ)
  (h₀ : x * y - x - y - 1 = 0) :
  (x - 1) * (y - 1) = 2 := by
  intros
  grind
