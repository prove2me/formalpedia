-- Prove2me | solution 1 for lean_workbook_plus_54024
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:58:37.090649+00:00
-- url     : https://prove2.me/submissions/6f114223-24f2-45b7-b68b-3adcaf5d88df

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ) : x - 1 < ⌊x⌋ ∧ ⌊x⌋ ≤ x := by
  exact ⟨Int.sub_one_lt_floor x,Int.floor_le x⟩
