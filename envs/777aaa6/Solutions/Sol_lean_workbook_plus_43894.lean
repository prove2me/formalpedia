-- Prove2me | solution 1 for lean_workbook_plus_43894
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:23:05.189984+00:00
-- url     : https://prove2.me/submissions/a6bf4930-abde-4c87-83fe-730a246b01cb

import Mathlib

private theorem schur_nonneg (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    0 ≤ u*(u-v)*(u-w) + v*(v-w)*(v-u) + w*(w-u)*(w-v) := by
  by_cases hz : u + v + w = 0
  · have hu0 : u = 0 := by linarith
    have hv0 : v = 0 := by linarith
    have hw0 : w = 0 := by linarith
    simp only [hu0, hv0, hw0, zero_mul, zero_add, le_refl]
  · have hs : 0 < u + v + w := lt_of_le_of_ne (by positivity) (Ne.symm hz)
    have hf : 0 < u + (v+w)/4 := by linarith
    have hp : 0 ≤ (u+(v+w)/4) *
        (u*(u-v)*(u-w) + v*(v-w)*(v-u) + w*(w-u)*(w-v)) := by
      calc
        0 ≤ v*w*(v-w)^2 + (w*u*(w-u)^2 + u*v*(u-v)^2)/4 +
            (2*u^2-v^2-w^2-u*v+2*v*w-w*u)^2/4 := by positivity
        _ = _ := by ring
    exact nonneg_of_mul_nonneg_right hp hf

theorem unrestricted_bound (a b c : ℝ) :
    a^10 + b^10 + c^10 +
      (b^4*c^4*(b^2+c^2) + c^4*a^4*(c^2+a^2) + a^4*b^4*(a^2+b^2)) +
      4*a^2*b^2*c^2*(a^4+b^4+c^4) ≥
      2*(b^2*c^2*(b^6+c^6) + c^2*a^2*(c^6+a^6) + a^2*b^2*(a^6+b^6)) +
      3*a^2*b^2*c^2*(b^2*c^2+c^2*a^2+a^2*b^2) := by
  have hq : 0 ≤ a^4+b^4+c^4-a^2*b^2-b^2*c^2-c^2*a^2 := by
    nlinarith only [sq_nonneg (a^2-b^2), sq_nonneg (b^2-c^2), sq_nonneg (c^2-a^2)]
  have hs := schur_nonneg (a^2) (b^2) (c^2) (sq_nonneg a) (sq_nonneg b) (sq_nonneg c)
  have hp := mul_nonneg hq hs
  nlinarith only [hp]

theorem solution (a b c : ℝ) (hx : a > 0 ∧ b > 0 ∧ c > 0)
    (hab : a+b > c) (hbc : b+c > a) (hca : a+c > b) :
    a^10 + b^10 + c^10 +
      (b^4*c^4*(b^2+c^2) + c^4*a^4*(c^2+a^2) + a^4*b^4*(a^2+b^2)) +
      4*a^2*b^2*c^2*(a^4+b^4+c^4) ≥
      2*(b^2*c^2*(b^6+c^6) + c^2*a^2*(c^6+a^6) + a^2*b^2*(a^6+b^6)) +
      3*a^2*b^2*c^2*(b^2*c^2+c^2*a^2+a^2*b^2) :=
  unrestricted_bound a b c
