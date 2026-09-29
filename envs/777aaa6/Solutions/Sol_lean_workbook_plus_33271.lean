-- Prove2me | solution 1 for lean_workbook_plus_33271
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:53:21.348296+00:00
-- url     : https://prove2.me/submissions/f4414730-8c15-47ae-9c94-a775559a842c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) (hab : a ≤ 0) (hbc : b ≤ 0) (hca : c ≤ 0) : max a c + max b c ≤ max (a + b) c := by
  intros
  grind
