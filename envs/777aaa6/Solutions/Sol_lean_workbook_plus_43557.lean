-- Prove2me | solution 1 for lean_workbook_plus_43557
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:40:37.774675+00:00
-- url     : https://prove2.me/submissions/3a9473ac-7909-473d-9b20-864c317bc261

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution {a b c d: ℝ} : 3 * (a + b + c + d) ^ 2 ≥ 8 * (a * b + a * c + a * d + b * c + b * d + c * d) := by
  intros
  have h : (0 : ℝ) ≤ (3 * (a + b + c + d) ^ 2) - (8 * (a * b + a * c + a * d + b * c + b * d + c * d)) := by
    calc
      0 ≤ (1 : ℝ) * ((d + ((-1) * c)))^2 + (1 : ℝ) * ((d + ((-1) * b)))^2 + (1 : ℝ) * ((d + ((-1) * a)))^2 + (1 : ℝ) * ((c + ((-1) * b)))^2 + (1 : ℝ) * ((c + ((-1) * a)))^2 + (1 : ℝ) * ((b + ((-1) * a)))^2 := by positivity
      _ = (3 * (a + b + c + d) ^ 2) - (8 * (a * b + a * c + a * d + b * c + b * d + c * d)) := by ring
  exact sub_nonneg.mp h
