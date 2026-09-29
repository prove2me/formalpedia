-- Prove2me | solution 1 for lean_workbook_plus_75043
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:46:27.511671+00:00
-- url     : https://prove2.me/submissions/fd4d8718-709f-42ef-bdf2-54e6e141035d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) (h₁ : 0 < x ∧ 0 < y) (h₂ : x + y = 2020) : 2 ≤ 2020 * x / y + y / (2020 * x) := by
  rcases h₁ with ⟨hx,hy⟩
  have hi : 2020*x/y+y/(2020*x)-2 = (2020*x-y)^2/(2020*x*y) := by field_simp; ring
  have hp : 0 ≤ (2020*x-y)^2/(2020*x*y) := by positivity
  linarith
