-- Prove2me | solution 1 for lean_workbook_plus_76439
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:20:09.788589+00:00
-- url     : https://prove2.me/submissions/c73f8e7d-184f-4ff6-babb-02c7624d2349

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ)
  (h₀ : (a - 1) * (b - 1) ≥ 0)
  (h₁ : c * (a - 1) * (b - 1) ≥ 0) :
  a^2 + b^2 + c^2 + 2 * b * c + 2 * c * a - 2 * c + 1 ≥ 2 * a * b + 2 * b * c + 2 * c * a := by
  intros
  have h : (0 : ℝ) ≤ (a^2 + b^2 + c^2 + 2 * b * c + 2 * c * a - 2 * c + 1) - (2 * a * b + 2 * b * c + 2 * c * a) := by
    calc
      0 ≤ (1 : ℝ) * ((1 + ((-1) * c)))^2 + (1 : ℝ) * ((b + ((-1) * a)))^2 := by positivity
      _ = (a^2 + b^2 + c^2 + 2 * b * c + 2 * c * a - 2 * c + 1) - (2 * a * b + 2 * b * c + 2 * c * a) := by ring
  exact sub_nonneg.mp h
