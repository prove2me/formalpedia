-- Prove2me | solution 1 for lean_workbook_plus_26739
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:03:06.116436+00:00
-- url     : https://prove2.me/submissions/e97dc97e-ee68-4233-85e3-2be68832b4cb

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a * b * c = 1) (h : a / (a + 2) + b / (b + 2) + c / (c + 1) = 1) : a * b * c ≤ 1 / 2 := by
  clear habc
  have hd₁ : 0 < a+2 := by positivity
  have hd₂ : 0 < b+2 := by positivity
  have hd₃ : 0 < c+1 := by positivity
  have hpoly : a*b+2*b*c+2*c*a+2*a*b*c=4 := by
    field_simp [ne_of_gt hd₁,ne_of_gt hd₂,ne_of_gt hd₃] at h
    nlinarith only [h]
  let p := a*b*c/4
  let q := a*b/4+b*c/2+c*a/2
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hq : q=1-2*p := by dsimp [p,q]; linarith
  have hA : 27*p^2 ≤ q^3 := by
    have hU : 0 ≤ a*b/4+b*c/2+(c*a/2)/4 := by positivity
    have hV : 0 ≤ c*a/2 := by positivity
    dsimp [p,q]
    nlinarith only [mul_nonneg (sq_nonneg (a*b/4+b*c/2-2*(c*a/2))) hU, mul_nonneg hV (sq_nonneg (a*b/4-b*c/2))]
  rw [hq] at hA
  have hgap : 0 ≤ (1-8*p)*(1+p)^2 := by nlinarith only [hA]
  have hp1 : 0 < (1+p)^2 := by positivity
  have hbnd := (mul_nonneg_iff_of_pos_right hp1).mp hgap
  dsimp [p] at hbnd
  linarith
