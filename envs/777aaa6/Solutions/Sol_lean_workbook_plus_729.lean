-- Prove2me | solution 1 for lean_workbook_plus_729
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:58:15.185724+00:00
-- url     : https://prove2.me/submissions/107e11e3-3725-4f64-a0df-05266fe82404

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (n : ℕ) :
  2 * Real.sqrt n + 1 / Real.sqrt (n + 1) ≤ 2 * Real.sqrt (n + 1) := by
  have hn : (0:ℝ)≤n := by positivity
  have hn1 : (0:ℝ)<n+1 := by positivity
  have hu := Real.sq_sqrt hn
  have hv := Real.sq_sqrt hn1.le
  have hp := Real.sqrt_pos.mpr hn1
  have hm : (1:ℝ)≤(2*Real.sqrt (n+1)-2*Real.sqrt n)*Real.sqrt (n+1) := by nlinarith only [hu,hv,sq_nonneg (Real.sqrt (n+1)-Real.sqrt n)]
  have hh := (div_le_iff₀ hp).mpr hm
  linarith
