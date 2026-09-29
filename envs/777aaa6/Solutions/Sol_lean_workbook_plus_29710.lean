-- Prove2me | solution 1 for lean_workbook_plus_29710
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:17:43.492069+00:00
-- url     : https://prove2.me/submissions/e427c581-5ff4-45aa-b881-029741683ed6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (h : 0 < a) (h2 : 0 < c) : (Real.sqrt (b ^ 2 - 4 * a * c) ≤ |b| - 2 → |b| ≥ 2 ∧ -4 * a * c ≤ -4 * |b| + 4) := by
  clear h h2
  intro hs
  have hp : 2≤abs b := by linarith [Real.sqrt_nonneg (b^2-4*a*c)]
  constructor
  · exact hp
  · have hq : b^2-4*a*c≤(abs b-2)^2 := by
      by_cases hd : 0≤b^2-4*a*c
      · have he := Real.sq_sqrt hd
        nlinarith [Real.sqrt_nonneg (b^2-4*a*c)]
      · nlinarith [sq_nonneg (abs b-2)]
    nlinarith [sq_abs b]
