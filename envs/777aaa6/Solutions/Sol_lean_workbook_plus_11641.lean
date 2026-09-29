-- Prove2me | solution 1 for lean_workbook_plus_11641
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:39:26.946267+00:00
-- url     : https://prove2.me/submissions/6a5ead8a-c654-43e0-bb11-a000d9ea22ea

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) : a ^ 2 + 4 * b ^ 2 - 4 * a * b ≥ 0 := by
  intros
  have h : (0 : ℝ) ≤ (a ^ 2 + 4 * b ^ 2 - 4 * a * b) - (0) := by
    calc
      0 ≤ (4 : ℝ) * ((b + ((-1 / 2) * a)))^2 := by positivity
      _ = (a ^ 2 + 4 * b ^ 2 - 4 * a * b) - (0) := by ring
  exact sub_nonneg.mp h
