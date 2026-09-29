-- Prove2me | solution 1 for lean_workbook_plus_50417
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:02:08.534637+00:00
-- url     : https://prove2.me/submissions/9d6e6ef9-1c7c-4389-b757-e935e35b141b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 + a / b) * (1 + b / c) * (1 + c / a) = 9 → 1 / a + 1 / b + 1 / c = 10 / (a + b + c) := by
  intros
  grind
