-- Prove2me | solution 1 for lean_workbook_plus_19940
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:06:52.046707+00:00
-- url     : https://prove2.me/submissions/fe526b23-8c1f-4633-a95b-54862532882c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a b : ℝ, (1 - 1 / (1 + |a|)) * (1 - 1 / (1 + |b|)) ≥ 0 := by
  intro a b
  have one : ∀t:ℝ,0≤1-1/(1+|t|) := by
    intro t
    have hp : 0<1+|t| := by positivity
    have h := (div_le_iff₀ hp).2 (show (1:ℝ)≤1*(1+|t|) by nlinarith [abs_nonneg t])
    linarith
  exact mul_nonneg (one a) (one b)
