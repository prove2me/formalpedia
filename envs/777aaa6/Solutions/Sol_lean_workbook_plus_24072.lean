-- Prove2me | solution 1 for lean_workbook_plus_24072
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:20:08.939379+00:00
-- url     : https://prove2.me/submissions/3fe99943-ebe0-4628-91b9-ec9dfee57a83

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) : (max (min a b) (min a c)) + max a (min b c) ≤ a + max b c := by
  intros
  grind
