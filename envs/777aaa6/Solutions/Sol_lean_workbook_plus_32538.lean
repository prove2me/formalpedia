-- Prove2me | solution 1 for lean_workbook_plus_32538
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:29:06.283249+00:00
-- url     : https://prove2.me/submissions/81723e44-2a52-4cf4-af2d-284199ed7a96

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a^2 + b^2 = 40) (hcd : c^2 + d^2 = 10) (h : a * c - b * d = 12) : a * d + b * c = 16 := by
  intros
  nlinarith
