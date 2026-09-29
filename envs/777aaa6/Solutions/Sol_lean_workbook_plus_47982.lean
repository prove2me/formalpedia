-- Prove2me | solution 1 for lean_workbook_plus_47982
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T03:34:45.675482+00:00
-- url     : https://prove2.me/submissions/e0a1617c-0e94-4b03-a4fc-227c705959d1

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace Pulse39

theorem sum_bound (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (h : u^2+v^2+w^2+2*u*v*w = 1) : u+v+w ≤ 3/2 := by
  let A := 1-u^2
  let B := 1-v^2
  let C := w+u*v
  have hr : 0 ≤ 2*u*v*w := by positivity
  have hA : 0 ≤ A := by dsimp [A]; nlinarith only [h,hr,sq_nonneg v,sq_nonneg w]
  have hB : 0 ≤ B := by dsimp [B]; nlinarith only [h,hr,sq_nonneg u,sq_nonneg w]
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hdet : A*B = C^2 := by dsimp [A,B,C]; nlinarith only [h]
  have hAB : 0 ≤ A+B-2*C := by
    by_contra hn
    have hprod : 0 < (2*C-A-B)*(2*C+A+B) := by
      apply mul_pos <;> linarith
    nlinarith only [hprod,sq_nonneg (A-B),hdet]
  dsimp [A,B,C] at hAB
  nlinarith only [hAB,sq_nonneg (1-u-v)]

theorem reciprocal_relation (a b c : ℝ)
    (h : 1/(a^2+1)+1/(b^2+1)+1/(c^2+1)=2) :
    (a*b)^2+(b*c)^2+(c*a)^2+2*(a*b)*(b*c)*(c*a)=1 := by
  have hh := h
  field_simp [ne_of_gt (show 0<a^2+1 by positivity),
    ne_of_gt (show 0<b^2+1 by positivity),
    ne_of_gt (show 0<c^2+1 by positivity)] at hh
  nlinarith only [hh]

theorem full_source_47982 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 1/(x^2+1)+1/(y^2+1)+1/(z^2+1)=2) : x*y+y*z+z*x ≤ 3/2 := by
  exact sum_bound (x*y) (y*z) (z*x) (by positivity) (by positivity) (by positivity)
    (reciprocal_relation x y z h)

end Pulse39

-- The exact posted premise is inconsistent because its denominators lost parentheses.
-- The genuine source theorem is established independently above.
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hx2 : x^2+1 > 0) (hy2 : y^2+1 > 0) (hz2 : z^2+1 > 0)
    (h : 1/x^2+1+1/y^2+1+1/z^2+1=2) : x*y+y*z+z*x ≤ 3/2 := by
  have hxq : 0 ≤ 1/x^2 := by positivity
  have hyq : 0 ≤ 1/y^2 := by positivity
  have hzq : 0 ≤ 1/z^2 := by positivity
  linarith
