-- Prove2me | solution 1 for lean_workbook_plus_19842
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:42:15.765123+00:00
-- url     : https://prove2.me/submissions/37175da5-3255-4a91-b051-b6c42b8e1fec

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution {a b c : ℝ} : 2 * (a * b + b * c + c * a) * (a * b + b * c + c * a) ≥ 6 * a * b * c * (a + b + c) := by
  intros
  have h : (0 : ℝ) ≤ (2 * (a * b + b * c + c * a) * (a * b + b * c + c * a)) - (6 * a * b * c * (a + b + c)) := by
    calc
      0 ≤ (1 : ℝ) * (((b * c) + ((-1) * a * c)))^2 + (1 : ℝ) * (((b * c) + ((-1) * a * b)))^2 + (1 : ℝ) * (((a * c) + ((-1) * a * b)))^2 := by positivity
      _ = (2 * (a * b + b * c + c * a) * (a * b + b * c + c * a)) - (6 * a * b * c * (a + b + c)) := by ring
  exact sub_nonneg.mp h
