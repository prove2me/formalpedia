-- Prove2me | solution 1 for lean_workbook_plus_75892
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:49:25.302598+00:00
-- url     : https://prove2.me/submissions/36c080ee-1c0b-4c07-a0c7-e0754d498b28

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) = 2) → a * b * c ≤ 9 / 64 := by
  intro h
  have hd₁ : 0 < 1+a := by positivity
  have hd₂ : 0 < 1+b := by positivity
  have hd₃ : 0 < 1+c := by positivity
  have hpoly : a*b+b*c+c*a+2*a*b*c=1 := by
    field_simp [ne_of_gt hd₁,ne_of_gt hd₂,ne_of_gt hd₃] at h
    nlinarith only [h]
  let p := a*b*c
  let q := a*b+b*c+c*a
  have hp : 0 < p := by dsimp [p]; positivity
  have hq : q=1-2*p := by dsimp [p,q]; linarith
  have hA : 27*p^2 ≤ q^3 := by
    have hU : 0 ≤ a*b+b*c+c*a/4 := by positivity
    have hV : 0 ≤ c*a := by positivity
    dsimp [p,q]
    nlinarith only [mul_nonneg (sq_nonneg (a*b+b*c-2*c*a)) hU, mul_nonneg hV (sq_nonneg (a*b-b*c))]
  rw [hq] at hA
  have hgap : 0 ≤ (1-8*p)*(1+p)^2 := by nlinarith only [hA]
  have hp1 : 0 < (1+p)^2 := by positivity
  have hbnd := (mul_nonneg_iff_of_pos_right hp1).mp hgap
  dsimp [p] at hbnd
  linarith
