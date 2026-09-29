-- Prove2me | Theorems.Thm_mme_stothers_phi233_entropy_tangent_stability
-- name    : mme_stothers_phi233_entropy_tangent_stability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:37:50.696623+00:00
-- url     : https://prove2.me/theorems/93b5a35c-22b8-47c3-ae46-a8712c1f39e4
-- title:
--   Tangent stability of the phi_233 maximum entropy under marginal perturbation
-- statement:
--   Let $(a,b,c,d)$ be a strictly positive normalized $\varphi_{233}$ profile with marginals $\sigma=2a+b$ and $\mu=a+c$, and suppose it satisfies the one-dimensional entropy stationarity equation. Let $(a',b',c',d')$ be any nonnegative normalized profile with perturbed marginals $\sigma'=2a'+b'$ and $\mu'=a'+c'$. Write $h(x)=-x\log x$, $u_b=-\log(b/2)-1$, $u_c=-\log(c/2)-1$, and $u_d=-\log(d/2)-1$. Then
--
--   $$
--   T(a',b',c',d')\le T(a,b,c,d)+(u_b-u_d)(\sigma'-\sigma)+(u_c-u_d)(\mu'-\mu),
--   $$
--
--   where $T(a,b,c,d)=4h(a/2)+2h(b/2)+2h(c/2)+2h(d/2)$.
--
--   This quantitative tangent bound is uniform over every competing same-marginal completion profile. Consequently, when rounded marginals approach the stationary marginals, the ambient maximum entropy cannot exceed the limiting target entropy by more than a vanishing error. This is the stability step needed in the exceptional $\varphi_{233}$ count.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Equation (3.6) and Lemma 5.1(v), pp. 360 and 366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; the inequality is the supporting-hyperplane form of the entropy optimization implicit in the asymptotic count.

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_stothers_phi233_entropy_tangent_stability
    (a b c d a' b' c' d' sigma mu sigma' mu' : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hc' : 0 ≤ c') (hd' : 0 ≤ d')
    (htotal : 2 * a + b + c + d = 1)
    (htotal' : 2 * a' + b' + c' + d' = 1)
    (hsigma : 2 * a + b = sigma) (hmu : a + c = mu)
    (hsigma' : 2 * a' + b' = sigma') (hmu' : a' + c' = mu')
    (hstation :
      2 * (-Real.log (a / 2) - 1) -
          2 * (-Real.log (b / 2) - 1) -
          (-Real.log (c / 2) - 1) +
          (-Real.log (d / 2) - 1) = 0) :
    4 * Real.negMulLog (a' / 2) +
          2 * Real.negMulLog (b' / 2) +
          2 * Real.negMulLog (c' / 2) +
          2 * Real.negMulLog (d' / 2) ≤
      4 * Real.negMulLog (a / 2) +
          2 * Real.negMulLog (b / 2) +
          2 * Real.negMulLog (c / 2) +
          2 * Real.negMulLog (d / 2) +
        ((-Real.log (b / 2) - 1) - (-Real.log (d / 2) - 1)) *
          (sigma' - sigma) +
        ((-Real.log (c / 2) - 1) - (-Real.log (d / 2) - 1)) *
          (mu' - mu) := by
  sorry
