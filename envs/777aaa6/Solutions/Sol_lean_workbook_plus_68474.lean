-- Prove2me | solution 1 for lean_workbook_plus_68474
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:27:28.102138+00:00
-- url     : https://prove2.me/submissions/6507eab1-e8d1-403d-8bdd-80017c83fdf9

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (u v x : ℝ)
  (h₀ : u = (2 + Real.sqrt 5)^(1 / 3))
  (h₁ : v = (2 - Real.sqrt 5)^(1 / 3))
  (h₂ : x = u + v)
  (h₃ : u^3 + v^3 = 4)
  (h₄ : u * v = -1) :
  x = 1 := by
  clear h₀ h₁
  have he : x^3 = u^3+v^3+3*(u*v)*(u+v) := by rw [h₂]; ring
  rw [h₃,h₄,← h₂] at he
  have hf : (x-1)*(x^2+x+4)=0 := by nlinarith only [he]
  have hp : x^2+x+4 ≠ 0 := ne_of_gt (by nlinarith [sq_nonneg (x+(1/2 : ℝ))])
  exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hp)
