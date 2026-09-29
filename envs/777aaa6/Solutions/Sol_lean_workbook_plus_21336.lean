-- Prove2me | solution 1 for lean_workbook_plus_21336
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:18:06.137977+00:00
-- url     : https://prove2.me/submissions/a07c6f03-a190-4ce9-b875-e37ec68bb988

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ)
  (h₀ : 0 < x ∧ 0 < y) :
  1 / (1 + x) + 1 / (1 + y) ≤ 1 / (1 + x * y) + 1 := by
  rcases h₀ with ⟨hx,hy⟩
  have hi : 1/(1+x*y)+1-(1/(1+x)+1/(1+y))=(x+y+x*y+x^2*y^2)/((1+x)*(1+y)*(1+x*y)) := by field_simp; ring
  have hp : 0≤(x+y+x*y+x^2*y^2)/((1+x)*(1+y)*(1+x*y)) := by positivity
  linarith
