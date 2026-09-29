-- Prove2me | solution 1 for lean_workbook_plus_65514
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:56:31.650139+00:00
-- url     : https://prove2.me/submissions/09803947-2d78-47b4-bf68-492fc133260d

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution : ∀ a b : ℝ, (|a| / (1 + |a|) + |b| / (1 + |b|) : ℝ) ≥ |a + b| / (1 + |a + b|) := by
  intro a b
  have ha := abs_nonneg a
  have hb := abs_nonneg b
  have hc := abs_nonneg (a+b)
  have hm : abs (a+b)/(1+abs (a+b)) ≤ (abs a+abs b)/(1+abs a+abs b) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [abs_add_le a b]
  have hi : abs a/(1+abs a)+abs b/(1+abs b)-(abs a+abs b)/(1+abs a+abs b) = abs a*abs b*(2+abs a+abs b)/((1+abs a)*(1+abs b)*(1+abs a+abs b)) := by
    field_simp
    ring
  have hn : 0 ≤ abs a*abs b*(2+abs a+abs b)/((1+abs a)*(1+abs b)*(1+abs a+abs b)) := by positivity
  linarith
