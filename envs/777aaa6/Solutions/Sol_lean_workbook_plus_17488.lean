-- Prove2me | solution 1 for lean_workbook_plus_17488
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:38:30.144971+00:00
-- url     : https://prove2.me/submissions/1a51c1fd-4f28-4dcf-90f0-98270cc4ed62

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (u v : ℝ) (h : u + 2 * v > 4) : 2 * u * v ≤ (u ^ 2 + 4 * v ^ 2) / 2 := by
  intros
  have h : (0 : ℝ) ≤ ((u ^ 2 + 4 * v ^ 2) / 2) - (2 * u * v) := by
    calc
      0 ≤ (2 : ℝ) * ((v + ((-1 / 2) * u)))^2 := by positivity
      _ = ((u ^ 2 + 4 * v ^ 2) / 2) - (2 * u * v) := by ring
  exact sub_nonneg.mp h
