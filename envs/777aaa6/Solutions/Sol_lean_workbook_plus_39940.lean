-- Prove2me | solution 1 for lean_workbook_plus_39940
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:06:30.719404+00:00
-- url     : https://prove2.me/submissions/932b6d6a-b236-4458-9260-e6990bf5b6e4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ) (hx : 0 < x ∧ x < 1) : (x^2/(1 - x) + (1 - x)^2/x) ≥ 1 := by
  have hden : 0 < 1-x := by linarith [hx.2]
  have he : x^2/(1-x)+(1-x)^2/x-1 = (2*x-1)^2/(x*(1-x)) := by
    field_simp [ne_of_gt hx.1, ne_of_gt hden]
    ring
  have hp := div_nonneg (sq_nonneg (2*x-1)) (mul_nonneg hx.1.le hden.le)
  linarith
