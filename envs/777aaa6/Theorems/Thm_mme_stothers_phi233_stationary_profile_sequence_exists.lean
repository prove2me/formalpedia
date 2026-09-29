-- Prove2me | Theorems.Thm_mme_stothers_phi233_stationary_profile_sequence_exists
-- name    : mme_stothers_phi233_stationary_profile_sequence_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:00:40.056881+00:00
-- url     : https://prove2.me/theorems/8c61fcd9-048a-468a-8fa1-f0a041a3e1ab
-- title:
--   Coherent positive stationary phi_233 profiles for interior marginal sequences
-- statement:
--   Let $(\sigma_n,\mu_n)$ be any sequence of marginal pairs lying strictly inside the feasible $\varphi_{233}$ region:
--
--   $$
--   0<\sigma_n<1,\qquad 0<\mu_n,\qquad \frac{\sigma_n}{2}+\mu_n<1.
--   $$
--
--   Then one can choose, coherently for every $n$, a strictly positive normalized profile $(A_n,B_n,C_n,D_n)$ with those marginals and satisfying the entropy critical equation
--
--   $$
--   A_n^2D_n=B_n^2C_n.
--   $$
--
--   This packages the pointwise critical-profile existence theorem into the sequence form needed by rounded-profile asymptotics.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, exceptional 233 constituent in Lemma 5.1, printed p. 367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. The critical equation is the Lagrange stationarity condition for the one-dimensional fixed-marginal entropy fiber.

import Mathlib.Tactic
import Theorems.Thm_mme_stothers_phi233_positive_critical_profile_exists

set_option autoImplicit false

theorem mme_stothers_phi233_stationary_profile_sequence_exists
    (sigma mu : ℕ → ℝ)
    (hsigma0 : ∀ n, 0 < sigma n)
    (hmu0 : ∀ n, 0 < mu n)
    (hsigma1 : ∀ n, sigma n < 1)
    (hcompat : ∀ n, sigma n / 2 + mu n < 1) :
    ∃ A B C D : ℕ → ℝ,
      (∀ n, 0 < A n) ∧ (∀ n, 0 < B n) ∧
      (∀ n, 0 < C n) ∧ (∀ n, 0 < D n) ∧
      (∀ n, 2 * A n + B n + C n + D n = 1) ∧
      (∀ n, 2 * A n + B n = sigma n) ∧
      (∀ n, A n + C n = mu n) ∧
      (∀ n, (A n) ^ (2 : ℕ) * D n = (B n) ^ (2 : ℕ) * C n) := by
  sorry
