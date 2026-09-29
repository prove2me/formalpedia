-- Prove2me | solution 1 for lean_workbook_plus_51710
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:12:43.786239+00:00
-- url     : https://prove2.me/submissions/efb71540-ff8d-4e5b-b736-688a896766af

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (1 / (1 + a) ^ 2 + 1 / (1 + b) ^ 2) ≥ 1 / (1 + a * b) := by
  have hi : 1/(1+a)^2+1/(1+b)^2-1/(1+a*b)=(a*b*(a-b)^2+(a*b-1)^2)/((1+a)^2*(1+b)^2*(1+a*b)) := by field_simp; ring
  have hp : 0≤(a*b*(a-b)^2+(a*b-1)^2)/((1+a)^2*(1+b)^2*(1+a*b)) := by positivity
  linarith
