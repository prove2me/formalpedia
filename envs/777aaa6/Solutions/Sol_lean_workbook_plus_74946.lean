-- Prove2me | solution 1 for lean_workbook_plus_74946
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:37:11.555569+00:00
-- url     : https://prove2.me/submissions/6d2949c1-f949-4606-b625-c16d8ce46e68

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) ≥ 9 / (2 * (a + b + c)) := by
  intros
  field_simp at * <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
