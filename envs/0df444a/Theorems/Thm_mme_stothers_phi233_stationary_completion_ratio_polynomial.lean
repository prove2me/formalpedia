-- Prove2me | Theorems.Thm_mme_stothers_phi233_stationary_completion_ratio_polynomial
-- name    : mme_stothers_phi233_stationary_completion_ratio_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:53:08.449748+00:00
-- url     : https://prove2.me/theorems/a8606729-8347-4fad-9be7-ab8fedf9b26a
-- title:
--   Polynomial same-marginal completion ratio for an exact stationary phi_233 profile
-- statement:
--   Let $\alpha,\beta,\gamma,\delta$ be positive integers with $2\alpha+\beta+\gamma+\delta=N$. Assume their two marginal ratios satisfy
--
--   $$
--   \frac{2\alpha+\beta}{N}<\frac23,\qquad \frac{\alpha+\gamma}{N}<\frac12,
--   $$
--
--   while the exact stationary equation $\alpha^2\delta=\beta^2\gamma$ holds. Let $S_0$ be the exact ten-label $\varphi_{233}$ target family and $S$ the full family with the same three mode marginals. Then
--
--   $$
--   |S|\le (2N+1)^{10}[6(2N+1)]^{10}|S_0|.
--   $$
--
--   Thus same-marginal ambiguity costs only an explicit degree-twenty polynomial for every exact positive stationary integer profile. This is the target-versus-ambient ratio needed by collision pruning in the exceptional $\varphi_{233}$ laser extraction.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Equation (3.6) and Lemma 5.1(v), pp. 360 and 366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; the displayed polynomial is an explicit finite version of the paper's subexponential completion loss.

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Definitions.Def_mme_stothers_phi233_profile_data
import Theorems.Thm_mme_stothers_phi233_exact_profile_entropy_polynomial_lower
import Theorems.Thm_mme_stothers_phi233_log_stationarity_of_critical_product
import Theorems.Thm_mme_stothers_phi233_stationary_marginal_address_entropy_upper

open MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_stothers_phi233_stationary_completion_ratio_polynomial
    (N alpha beta gamma delta : ℕ)
    (hN : 0 < N) (haN : 0 < alpha) (hbN : 0 < beta)
    (hcN : 0 < gamma) (hdN : 0 < delta)
    (hsum : 2 * alpha + beta + gamma + delta = N)
    (hsigmaUpper :
      ((2 * alpha + beta : ℕ) : ℝ) / (N : ℝ) < 2 / 3)
    (hmuUpper :
      ((alpha + gamma : ℕ) : ℝ) / (N : ℝ) < 1 / 2)
    (hcritical : alpha ^ (2 : ℕ) * delta =
      beta ^ (2 : ℕ) * gamma) :
    (Nat.card
        (MME.StothersFourth.Phi233.MarginalAddress
          N alpha beta gamma delta) : ℝ) ≤
      ((((2 * N + 1 : ℕ) : ℝ)) ^ 10 *
        (6 * (((2 * N + 1 : ℕ) : ℝ))) ^ 10) *
        (Nat.card
          (MME.StothersFourth.Phi233.ExactProfileAddress
            N alpha beta gamma delta) : ℝ) := by
  sorry
