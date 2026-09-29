-- Prove2me | solution 1 for lean_workbook_plus_40264
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:42:22.90404+00:00
-- url     : https://prove2.me/submissions/b12139c6-0339-46a7-9d91-0406eeeda2b1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (habc : a + b + c = 0) : (a^3 + b^3 + c^3 + a^2 - b^2 - c^2) / (b * c) = 3 * a + 2 := by
  intros
  grind
