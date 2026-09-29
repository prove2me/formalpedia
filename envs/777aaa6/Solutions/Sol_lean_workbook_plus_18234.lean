-- Prove2me | solution 1 for lean_workbook_plus_18234
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:28:27.28171+00:00
-- url     : https://prove2.me/submissions/e613d607-04d2-4a2f-b890-537f126614db

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n : ℝ) : 100 * n - 5050 = 0 ↔ n = 101 / 2 := by
  intros
  grind
