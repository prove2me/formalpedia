-- Prove2me | solution 1 for lean_workbook_plus_3909
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:56:39.288428+00:00
-- url     : https://prove2.me/submissions/379a5e7a-0e73-4de0-98ec-b9c1f8d7ee83

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℂ) : x ^ 2 - 64 = 0 ↔ x = 8 ∨ x = -8 := by
  intros
  grind
