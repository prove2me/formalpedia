-- Prove2me | solution 1 for lean_workbook_plus_31643
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:43:43.161165+00:00
-- url     : https://prove2.me/submissions/3cf6c5e2-67bd-4461-a158-efb745ae7a5c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) : 3 * a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 - 8 * b * c ^ 2 * a + b ^ 2 * c ^ 2 + 3 * c ^ 4 ≥ 0 := by
  intros
  have h : (0 : ℝ) ≤ (3 * a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 - 8 * b * c ^ 2 * a + b ^ 2 * c ^ 2 + 3 * c ^ 4) - (0) := by
    calc
      0 ≤ (3 : ℝ) * (((c ^ 2) + ((-1) * a * b)))^2 + (1 : ℝ) * (((b * c) + ((-1) * a * c)))^2 := by positivity
      _ = (3 * a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 - 8 * b * c ^ 2 * a + b ^ 2 * c ^ 2 + 3 * c ^ 4) - (0) := by ring
  exact sub_nonneg.mp h
