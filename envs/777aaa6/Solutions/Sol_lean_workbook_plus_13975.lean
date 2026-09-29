-- Prove2me | solution 1 for lean_workbook_plus_13975
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:04:34.624925+00:00
-- url     : https://prove2.me/submissions/dbaa5894-495f-46d8-a691-30c3f5520779

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∃! x : ℝ, x^7 + 1 = 0 := by
  refine ⟨-1,by norm_num,?_⟩
  intro x hx
  have hp : 0<x^6-x^5+x^4-x^3+x^2-x+1 := by
    nlinarith only [sq_nonneg (x^3-x^2/2),sq_nonneg (x^2-2*x/3),sq_nonneg (x-3/4)]
  have he : (x+1)*(x^6-x^5+x^4-x^3+x^2-x+1)=0 := by nlinarith only [hx]
  have hz := (mul_eq_zero.mp he).resolve_right (ne_of_gt hp)
  linarith
