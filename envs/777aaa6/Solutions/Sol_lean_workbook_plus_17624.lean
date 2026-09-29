-- Prove2me | solution 1 for lean_workbook_plus_17624
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:53:47.882229+00:00
-- url     : https://prove2.me/submissions/a78d6e94-c045-4c35-a090-47a34d5fbe7d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ) (hx : 0 < x) :
  2 * (1 / x) ≥ 4 / (1 + x) ^ 2 ↔ (1 + x) ^ 2 ≥ 4 * x := by
  have hsq : (1+x)^2≥4*x := by nlinarith only [sq_nonneg (x-1)]
  have hL : 4/(1+x)^2 ≤ 2*(1/x) := by
    have hp : 0<(1+x)^2 := by positivity
    rw [show 2*(1/x)=(2:ℝ)/x by ring]
    apply (div_le_div_iff₀ hp hx).mpr
    nlinarith only [sq_nonneg x]
  exact ⟨fun _ => hsq,fun _ => hL⟩
