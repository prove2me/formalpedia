-- Prove2me | solution 1 for lean_workbook_plus_51582
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:46:45.110723+00:00
-- url     : https://prove2.me/submissions/f47808bf-f570-43a1-872f-7d9f10528e3b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) :
  a^4 + a^4 + a^4 + b^4 ≥ 4 * (a^3 * b) ∧
  b^4 + b^4 + b^4 + c^4 ≥ 4 * (b^3 * c) ∧
  c^4 + c^4 + c^4 + a^4 ≥ 4 * (c^3 * a) := by
  have young : ∀ x y:ℝ, 3*x^4+y^4 ≥ 4*x^3*y := by
    intro x y
    have hp := mul_nonneg (sq_nonneg (x-y)) (show 0 ≤ 2*x^2+(x+y)^2 by positivity)
    nlinarith only [hp]
  constructor
  · nlinarith [young a b]
  · constructor
    · nlinarith [young b c]
    · nlinarith [young c a]
