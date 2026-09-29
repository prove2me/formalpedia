-- Prove2me | Theorems.Thm_mme_stothers_phi233_stationary_marginal_address_entropy_upper
-- name    : mme_stothers_phi233_stationary_marginal_address_entropy_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:49:20.410644+00:00
-- url     : https://prove2.me/theorems/0aa95770-4504-4628-97ff-9e4c4479a9cc
-- title:
--   Sharp ambient entropy bound from a stationary phi_233 profile
-- statement:
--   Fix positive interior marginal ratios $0<\sigma<2/3$ and $0<\mu<1/2$ that equal the exact integer marginals $(2\alpha+\beta)/N$ and $(\alpha+\gamma)/N$. Let $(a,b,c,d)$ be a positive normalized stationary $\varphi_{233}$ profile with $2a+b=\sigma$ and $a+c=\mu$. Then the full same-marginal completion family $S$ satisfies
--
--   $$
--   |S|\le (2N+1)^{10}\exp\!\left(2N\left[4h(a/2)+2h(b/2)+2h(c/2)+2h(d/2)\right]\right),
--   $$
--
--   where $h(x)=-x\log x$.
--
--   This removes the existential entropy maximizer from the ambient count: any positive stationary profile supplies the sharp exponential rate. It is the denominator estimate paired with the exact-profile multinomial lower bound in the exceptional $\varphi_{233}$ extraction.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Equation (3.6) and Lemma 5.1(v), pp. 360 and 366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Definitions.Def_mme_stothers_phi233_profile_data
import Theorems.Thm_mme_stothers_phi233_marginal_address_entropy_upper
import Theorems.Thm_mme_stothers_phi233_entropy_tangent_stability

open MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_stothers_phi233_stationary_marginal_address_entropy_upper
    (N alpha beta gamma delta : ℕ) (hN : 0 < N)
    (sigma mu a b c d : ℝ)
    (hsigma0 : 0 < sigma) (hsigmaUpper : sigma < 2 / 3)
    (hmu0 : 0 < mu) (hmuUpper : mu < 1 / 2)
    (hsigmaRatio : ((2 * alpha + beta : ℕ) : ℝ) / (N : ℝ) = sigma)
    (hmuRatio : ((alpha + gamma : ℕ) : ℝ) / (N : ℝ) = mu)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (htotal : 2 * a + b + c + d = 1)
    (hab : 2 * a + b = sigma) (hac : a + c = mu)
    (hstation :
      2 * (-Real.log (a / 2) - 1) -
          2 * (-Real.log (b / 2) - 1) -
          (-Real.log (c / 2) - 1) +
          (-Real.log (d / 2) - 1) = 0) :
    (Nat.card
        (MME.StothersFourth.Phi233.MarginalAddress
          N alpha beta gamma delta) : ℝ) ≤
      (((2 * N + 1 : ℕ) : ℝ)) ^ 10 *
        Real.exp (((2 * N : ℕ) : ℝ) *
          (4 * Real.negMulLog (a / 2) +
            2 * Real.negMulLog (b / 2) +
            2 * Real.negMulLog (c / 2) +
            2 * Real.negMulLog (d / 2))) := by
  sorry
