-- Prove2me | Theorems.Thm_mme_stothers_phi233_positive_critical_profile_exists
-- name    : mme_stothers_phi233_positive_critical_profile_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:44:29.248055+00:00
-- url     : https://prove2.me/theorems/1288d8fd-b43a-462c-b03f-e580c7d65961
-- title:
--   Existence of a positive critical phi_233 profile
-- statement:
--   Let the two independent $\varphi_{233}$ marginals satisfy
--
--   $$
--   0<\sigma<1,\qquad 0<\mu,\qquad \frac{\sigma}{2}+\mu<1.
--   $$
--
--   Then there is a strictly positive normalized profile $(a,b,c,d)$ such that
--
--   $$
--   2a+b+c+d=1,\qquad 2a+b=\sigma,\qquad a+c=\mu,\qquad a^2d=b^2c.
--   $$
--
--   The last identity is the critical-point equation for the one-dimensional fixed-marginal entropy fibre. This theorem supplies an interior stationary profile without choosing a nonconstructive entropy maximizer, enabling a direct tangent-certificate proof of the exceptional $\varphi_{233}$ count.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), the profile optimization in Lemma 5.1(v) and Equation (3.6), pp. 360 and 366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_stothers_phi233_positive_critical_profile_exists
    (sigma mu : ℝ) (hsigma0 : 0 < sigma) (hmu0 : 0 < mu)
    (hsigma1 : sigma < 1) (hcompat : sigma / 2 + mu < 1) :
    ∃ a b c d : ℝ,
      0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      2 * a + b + c + d = 1 ∧
      2 * a + b = sigma ∧ a + c = mu ∧
      a ^ (2 : ℕ) * d = b ^ (2 : ℕ) * c := by
  sorry
