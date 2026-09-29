-- Prove2me | solution 1 for lean_workbook_plus_48725
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:06:34.455425+00:00
-- url     : https://prove2.me/submissions/c64d2928-e550-40b5-93b0-a7b9d07f3bcc

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ) : |x^2 - 4*x - 39601| ≥ |x^2 + 4*x - 39601| → x ≤ 199 := by
  intro h
  by_contra hn
  have hp : 0 < x := by linarith
  have hq : 0 < x^2-39601 := by nlinarith
  have hr : 0 < x^2+4*x-39601 := by linarith
  rw [abs_of_pos hr] at h
  have hl : |x^2-4*x-39601| < x^2+4*x-39601 := by
    apply abs_lt.mpr
    constructor <;> linarith
  linarith
