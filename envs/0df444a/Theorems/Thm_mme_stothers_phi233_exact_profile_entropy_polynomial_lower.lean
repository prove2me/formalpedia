-- Prove2me | Theorems.Thm_mme_stothers_phi233_exact_profile_entropy_polynomial_lower
-- name    : mme_stothers_phi233_exact_profile_entropy_polynomial_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:33:12.532144+00:00
-- url     : https://prove2.me/theorems/2372caa4-f977-4685-96b4-fba8cf853f92
-- title:
--   Polynomial-loss entropy lower bound for the exact phi_233 profile
-- statement:
--   Let $N>0$ and let $2\alpha+\beta+\gamma+\delta=N$. For the exact $\varphi_{233}$ target family $S_0$ with ten-label multiplicities $(\alpha,\beta,\alpha,\gamma,\delta,\delta,\gamma,\alpha,\beta,\alpha)$, define $h(x)=-x\log x$ (continuously extended by $h(0)=0$). Then
--
--   $$
--   \exp\!\left(2N\left[4h\!\left(\frac{\alpha}{2N}\right)+2h\!\left(\frac{\beta}{2N}\right)+2h\!\left(\frac{\gamma}{2N}\right)+2h\!\left(\frac{\delta}{2N}\right)\right]\right)\le [6(2N+1)]^{10}|S_0|.
--   $$
--
--   Thus the exact target family realizes its multinomial entropy rate with only an explicit degree-ten polynomial loss. This is the numerator estimate needed to compare $S_0$ with the full same-marginal completion family in the exceptional type-2 analysis.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Equation (3.6) and Lemma 5.1(v), pp. 360 and 366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; the explicit polynomial factor is the standard finite multinomial entropy estimate.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_stothers_phi233_exact_profile_card
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem mme_stothers_phi233_exact_profile_entropy_polynomial_lower
    (N alpha beta gamma delta : ℕ) (hN : 0 < N)
    (hsum : 2 * alpha + beta + gamma + delta = N) :
    Real.exp
        (((2 * N : ℕ) : ℝ) *
          (4 * Real.negMulLog ((alpha : ℝ) / ((2 * N : ℕ) : ℝ)) +
            2 * Real.negMulLog ((beta : ℝ) / ((2 * N : ℕ) : ℝ)) +
            2 * Real.negMulLog ((gamma : ℝ) / ((2 * N : ℕ) : ℝ)) +
            2 * Real.negMulLog ((delta : ℝ) / ((2 * N : ℕ) : ℝ)))) ≤
      (6 * (((2 * N + 1 : ℕ) : ℝ))) ^ 10 *
        (Nat.card
          (MME.StothersFourth.Phi233.ExactProfileAddress
            N alpha beta gamma delta) : ℝ) := by
  sorry
