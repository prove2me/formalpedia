-- Prove2me | solution 1 for lean_workbook_plus_21186
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:53:41.621787+00:00
-- url     : https://prove2.me/submissions/cac48929-7928-4b2d-8a62-842ca08b155e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n : ℕ) : 1 + (3 ^ (n - 1) - 1) / 2 = (1 + 3 ^ (n - 1)) / 2 := by
  intros
  grind
