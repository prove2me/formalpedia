-- Prove2me | solution 1 for lean_workbook_plus_35923
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:23:33.675569+00:00
-- url     : https://prove2.me/submissions/cb5678bf-06d0-4df7-9f60-cad834a5794c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c d : ℝ) (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d ↔ a * d = b * c := by
  intros
  grind
