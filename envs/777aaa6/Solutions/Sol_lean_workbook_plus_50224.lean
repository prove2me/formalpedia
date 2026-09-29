-- Prove2me | solution 1 for lean_workbook_plus_50224
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:14:48.979302+00:00
-- url     : https://prove2.me/submissions/9be694c8-7bab-47e9-b9ea-bb77e65c38fb

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (v t : ℝ)
  (h₀ : 0 < v ∧ 0 < t)
  (h₁ : 3124 * v * t / 629 + 17.9 * v * t = 1) :
  17.9 * v * t / (17.9 * v * t + 3124 * v * t / 629) = 112591 / 143831 := by
  clear h₁
  have hv : 0 < v := h₀.1
  have ht : 0 < t := h₀.2
  have hd : 0 < 17.9*v*t+3124*v*t/629 := by positivity
  apply (div_eq_iff (ne_of_gt hd)).2
  ring
