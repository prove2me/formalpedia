-- Prove2me | solution 1 for lean_workbook_plus_48471
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:51:10.577967+00:00
-- url     : https://prove2.me/submissions/1b55a2bf-6d31-402e-91f7-f00fb87c2f72

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ) (h : ∀ x ∈ Set.Icc (-1) 1, abs (a * x ^ 2 + b * x + c) ≤ 1) :
  abs a + abs b + abs c ≤ 4 := by
  have h0 := h 0 (by constructor <;> norm_num)
  have hp := h 1 (by constructor <;> norm_num)
  have hm := h (-1) (by constructor <;> norm_num)
  clear h
  have h0a := abs_le.mp h0
  have hpa := abs_le.mp hp
  have hma := abs_le.mp hm
  have ha : |a|≤2 := abs_le.mpr (by constructor <;> linarith [h0a.1,h0a.2,hpa.1,hpa.2,hma.1,hma.2])
  have hb : |b|≤1 := abs_le.mpr (by constructor <;> linarith [hpa.1,hpa.2,hma.1,hma.2])
  have hc : |c|≤1 := by simpa using h0
  linarith
