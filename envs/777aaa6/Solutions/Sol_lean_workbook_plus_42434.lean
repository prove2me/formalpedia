-- Prove2me | solution 1 for lean_workbook_plus_42434
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:53:12.789587+00:00
-- url     : https://prove2.me/submissions/4823491f-e384-4d3f-b121-50cc4d39e62a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : 3*a = 4*b) (hbc : 5*b = 6*c) : c/(a+b) = 5/14 := by
  intros
  grind
