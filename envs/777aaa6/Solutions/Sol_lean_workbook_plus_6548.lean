-- Prove2me | solution 1 for lean_workbook_plus_6548
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:47:01.88273+00:00
-- url     : https://prove2.me/submissions/079fd7ec-a944-4c34-9400-c647b6c4463c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x^5 + y^5 = 2) : (x^2 + y^6)*(x^8 + y^4) + 2 ≥ x^10 + y^10 := by
  clear hx hy h
  have h₁ : 0 ≤ x ^ 2 * y ^ 4 := by positivity
  have h₂ : 0 ≤ x ^ 8 * y ^ 6 := by positivity
  nlinarith only [h₁, h₂]
