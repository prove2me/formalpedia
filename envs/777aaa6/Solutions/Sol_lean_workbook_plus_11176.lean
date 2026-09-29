-- Prove2me | solution 1 for lean_workbook_plus_11176
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:19:25.804173+00:00
-- url     : https://prove2.me/submissions/9dd8b8e5-6d2f-43c7-86a6-19d100fa90c4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution {a b c d : ℝ} :
  3 * ((a^2 + b^2 + c^2) + (b^2 + c^2 + d^2) + (c^2 + d^2 + a^2) + (d^2 + a^2 + b^2)) ≥
  (a + b + c)^2 + (b + c + d)^2 + (c + d + a)^2 + (d + a + b)^2 := by
  intros
  have h : (0 : ℝ) ≤ (3 * ((a^2 + b^2 + c^2) + (b^2 + c^2 + d^2) + (c^2 + d^2 + a^2) + (d^2 + a^2 + b^2))) - ((a + b + c)^2 + (b + c + d)^2 + (c + d + a)^2 + (d + a + b)^2) := by
    calc
      0 ≤ (2 : ℝ) * ((d + ((-1) * c)))^2 + (2 : ℝ) * ((d + ((-1) * b)))^2 + (2 : ℝ) * ((d + ((-1) * a)))^2 + (2 : ℝ) * ((c + ((-1) * b)))^2 + (2 : ℝ) * ((c + ((-1) * a)))^2 + (2 : ℝ) * ((b + ((-1) * a)))^2 := by positivity
      _ = (3 * ((a^2 + b^2 + c^2) + (b^2 + c^2 + d^2) + (c^2 + d^2 + a^2) + (d^2 + a^2 + b^2))) - ((a + b + c)^2 + (b + c + d)^2 + (c + d + a)^2 + (d + a + b)^2) := by ring
  exact sub_nonneg.mp h
