-- Prove2me | solution 1 for lean_workbook_plus_18647
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:23:54.099071+00:00
-- url     : https://prove2.me/submissions/961c1453-a24a-4be0-8221-14bfa4bb9122

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) : (a^2 + 1) * (b^2 + 1) ≥ a * (b^2 + 1) + b * (a^2 + 1) := by
  intros
  have h : (0 : ℝ) ≤ ((a^2 + 1) * (b^2 + 1)) - (a * (b^2 + 1) + b * (a^2 + 1)) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * ((1 + ((-1) * b)))^2 + ((1 / 2) : ℝ) * ((1 + ((-1) * a)))^2 + ((1 / 2) : ℝ) * ((b + ((-1) * a * b)))^2 + ((1 / 2) : ℝ) * ((a + ((-1) * a * b)))^2 := by positivity
      _ = ((a^2 + 1) * (b^2 + 1)) - (a * (b^2 + 1) + b * (a^2 + 1)) := by ring
  exact sub_nonneg.mp h
