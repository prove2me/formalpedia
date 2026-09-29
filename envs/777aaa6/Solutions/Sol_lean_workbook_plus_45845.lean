-- Prove2me | solution 1 for lean_workbook_plus_45845
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:41:44.001212+00:00
-- url     : https://prove2.me/submissions/1cb3428b-d89f-47d4-9ea3-9c804449cab7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) (hx : x = 7) : (x - 1) / x * (x - 2) / (x - 1) * (x - 3) / (x - 2) = 4 / 7 := by
  intros
  grind
