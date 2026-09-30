-- Prove2me | solution 1 for lean_workbook_plus_69800
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:04:58.880253+00:00
-- url     : https://prove2.me/submissions/958b709a-b83a-465d-bca7-4fcd0055906f

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

private theorem cubic_tangent (t : ℝ) (h : 0 ≤ t) : 3*t ≤ t^3+2 := by
  have hp := mul_nonneg (sq_nonneg (t-1)) (by linarith : 0 ≤ t+2)
  nlinarith only [hp]

theorem solution (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (habc : a*b*c*d = 1)
    (h : a^3+b^3+c^3+d^3+a*b*c*d = 5) : a*b+c*d ≤ 2 := by
  have hsum : a+b+c+d ≤ 4 := by
    linarith only [habc, h, cubic_tangent a ha, cubic_tangent b hb,
      cubic_tangent c hc, cubic_tangent d hd]
  have hsum0 := add_nonneg (add_nonneg (add_nonneg ha hb) hc) hd
  have hsquare : (a+b+c+d)^2 ≤ 16 := by
    have hs := (sq_le_sq₀ hsum0 (by norm_num : (0 : ℝ) ≤ 4)).mpr hsum
    nlinarith only [hs]
  have hab : 4*(a*b) ≤ (a+b)^2 := by nlinarith only [sq_nonneg (a-b)]
  have hcd : 4*(c*d) ≤ (c+d)^2 := by nlinarith only [sq_nonneg (c-d)]
  have hprod := mul_le_mul hab hcd
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (mul_nonneg hc hd))
    (sq_nonneg (a+b))
  have hcross0 := mul_nonneg (add_nonneg ha hb) (add_nonneg hc hd)
  have hcross : 4 ≤ (a+b)*(c+d) := by
    apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 4) hcross0).mp
    nlinarith only [hprod, habc]
  nlinarith only [hsquare, hab, hcd, hcross]
