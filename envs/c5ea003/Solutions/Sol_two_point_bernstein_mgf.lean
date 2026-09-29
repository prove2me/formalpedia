-- Prove2me | solution 1 for two_point_bernstein_mgf
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-22T02:18:21.600897+00:00
-- url     : https://prove2.me/submissions/e3bac003-81ea-4662-bef4-6e769acc4779

import Theorems.Thm_exp_le_quad
import Mathlib.Analysis.SpecialFunctions.Exp
set_option maxHeartbeats 1000000
open scoped BigOperators

theorem solution (p a b : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hcent : p * a + (1 - p) * b = 0) (ha : a ≤ 1) (hb : b ≤ 1) :
    p * Real.exp a + (1 - p) * Real.exp b ≤
      Real.exp (p * a^2 + (1 - p) * b^2) := by
  have hEa := exp_le_quad a ha
  have hEb := exp_le_quad b hb
  have h1p : (0:ℝ) ≤ 1 - p := by linarith
  have hV : (0:ℝ) ≤ p * a^2 + (1 - p) * b^2 := by positivity
  -- p e^a + (1-p) e^b ≤ 1 + (pa+(1-p)b) + V = 1 + 0 + V = 1 + V
  have hcomb : p * Real.exp a + (1 - p) * Real.exp b ≤ 1 + (p*a^2 + (1-p)*b^2) := by
    have h := add_le_add (mul_le_mul_of_nonneg_left hEa hp0)
                         (mul_le_mul_of_nonneg_left hEb h1p)
    nlinarith [h, hcent]
  -- 1 + V ≤ exp V
  have hexpV : 1 + (p*a^2 + (1-p)*b^2) ≤ Real.exp (p*a^2 + (1-p)*b^2) := by
    have := Real.add_one_le_exp (p*a^2 + (1-p)*b^2); linarith
  linarith [hcomb, hexpV]
