-- Prove2me | solution 1 for lean_workbook_plus_44319
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:54:36.847152+00:00
-- url     : https://prove2.me/submissions/d3b557c5-592d-413f-8928-60cc3439b77c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem polynomial_remainder (u v : ℝ) :
    16*(u^4+v^4+(u^2+1)*(v^2+1)-((v+1)*u^3+(u+1)*v^3+u+v)) =
      (u+v-2)^2*((u+v)^2+4)+
        (u-v)^2*(5*(u-v)^2+(3*(u+v)-2)^2+(u+v)^2+4) := by
  ring

theorem polynomial_bound (u v : ℝ) :
    (v+1)*u^3+(u+1)*v^3+u+v ≤ u^4+v^4+(u^2+1)*(v^2+1) := by
  have h : 0 ≤ (u+v-2)^2*((u+v)^2+4)+
      (u-v)^2*(5*(u-v)^2+(3*(u+v)-2)^2+(u+v)^2+4) := by positivity
  nlinarith only [polynomial_remainder u v, h]

theorem unrestricted_bound (x y : ℝ) :
    (abs y+1)*abs x^3+(abs x+1)*abs y^3+abs x+abs y ≤
      x^4+y^4+(x^2+1)*(y^2+1) := by
  have hx4 : |x|^4 = x^4 := by
    calc
      _ = (|x|^2)^2 := by ring
      _ = (x^2)^2 := by rw [sq_abs]
      _ = _ := by ring
  have hy4 : |y|^4 = y^4 := by
    calc
      _ = (|y|^2)^2 := by ring
      _ = (y^2)^2 := by rw [sq_abs]
      _ = _ := by ring
  simpa only [hx4, hy4, sq_abs] using polynomial_bound |x| |y|

theorem solution (x y : ℝ) (hx : x > 0) (hy : y > 0) :
    x^4+y^4+(x^2+1)*(y^2+1) ≥
      (abs y+1)*abs x^3+(abs x+1)*abs y^3+abs x+abs y :=
  unrestricted_bound x y
