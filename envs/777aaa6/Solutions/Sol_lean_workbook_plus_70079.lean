-- Prove2me | solution 1 for lean_workbook_plus_70079
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:01:00.279384+00:00
-- url     : https://prove2.me/submissions/d17b79cb-2bf4-49dd-8adb-3e8b0c5259b9

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n : ℤ) : n - 3 ∈ ({-15, -5, -3, -1, 1, 3, 5, 15} : Finset ℤ) ↔ n ∈ ({-12, -2, 0, 2, 4, 6, 8, 18} : Finset ℤ) := by
  intros
  grind
