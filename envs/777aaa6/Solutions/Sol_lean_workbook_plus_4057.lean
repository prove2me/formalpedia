-- Prove2me | solution 1 for lean_workbook_plus_4057
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:38:44.753946+00:00
-- url     : https://prove2.me/submissions/c799a9c2-099d-4e9c-9872-674a10ef5359

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) : (a / (2 * a + 1) + b / (2 * b + 1) + c / (2 * c + 1)) ≥ 1 := by
  have one : ∀ x:ℝ, 1 ≤ x → (1:ℝ)/3 ≤ x/(2*x+1) := by
    intro x hx
    apply (le_div_iff₀ (by linarith : 0 < 2*x+1)).2
    linarith
  linarith [one a ha,one b hb,one c hc]
