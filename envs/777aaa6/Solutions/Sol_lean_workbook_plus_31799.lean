-- Prove2me | solution 1 for lean_workbook_plus_31799
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T02:26:40.837925+00:00
-- url     : https://prove2.me/submissions/c3fa2b10-53af-4992-98f8-4de31461606f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

private theorem workbook_source_31799 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a*b+a*c+b*c=3) :
    a^3+b^3+c^3+1 ≥ 4*(a*b*c)^3 := by
  have product_bound (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
      (hsum : x+y+z=3) : x*y*z ≤ 1 := by
    have hx4 : 0 ≤ 4-x := by linarith
    have hpos : 0 ≤ (4-x)*(x-1)^2+x*(y-z)^2 := by positivity
    have hzexpr : z=3-x-y := by linarith
    have hid : 4-4*x*y*z=(4-x)*(x-1)^2+x*(y-z)^2 := by
      rw [hzexpr]
      ring
    linarith
  have hpairs : (a*b)*(a*c)*(b*c) ≤ 1 :=
    product_bound (a*b) (a*c) (b*c) (by positivity) (by positivity) (by positivity) h
  have hr0 : 0 ≤ a*b*c := by positivity
  have hr1 : a*b*c ≤ 1 := by nlinarith
  have hfactor : 0 ≤ (1-a*b*c)*(2*(a*b*c)+1)^2 := mul_nonneg (sub_nonneg.mpr hr1) (sq_nonneg _)
  have hcubes : 3*a*b*c ≤ a^3+b^3+c^3 := by
    have hd : 0 ≤ (a+b+c)*((a-b)^2+(b-c)^2+(c-a)^2) := by positivity
    nlinarith
  nlinarith

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : a ^ 3 + b ^ 3 + c ^ 3 + 1 ≥ 4 * (a * b * c) ^ 3   := by
  have hcubes : 3 * a * b * c ≤ a ^ 3 + b ^ 3 + c ^ 3 := by
    have hd : 0 ≤ (a+b+c)*((a-b)^2+(b-c)^2+(c-a)^2) := by positivity
    nlinarith
  rw [habc]
  nlinarith
