-- Prove2me | Theorems.Thm_mme_stothers_phi224_exact_profile_entropy_polynomial_lower
-- name    : mme_stothers_phi224_exact_profile_entropy_polynomial_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T09:50:01.221021+00:00
-- url     : https://prove2.me/theorems/39e88e58-bfef-4b66-bfb0-5557c8fd69d6
-- title:
--   Polynomial-loss entropy lower bound for exact phi_224 profiles
-- statement:
--   Let $N>0$ and $\alpha+2\beta+\gamma+\delta=N$. The exact $\varphi_{224}$ profile family satisfies
--
--   $$
--   \exp\!\left(2N\left[2h\!\left(\frac{\alpha}{2N}\right)+4h\!\left(\frac{\beta}{2N}\right)+2h\!\left(\frac{\gamma}{2N}\right)+h\!\left(\frac{2\delta}{2N}\right)\right]\right)
--   \leq
--   \bigl(6(2N+1)\bigr)^9\,|S_0|,
--   $$
--
--   where $h(t)=-t\log t$ and $S_0$ is the exact-profile word family. Thus the exact family realizes its multinomial entropy rate up to an explicit polynomial loss.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), the type-2 profile counts in equations (3.5)--(3.6) and Lemma 5.1(iv), pp. 359--360 and 365--366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi224_profile_data
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_stothers_phi224_exact_profile_card
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower

open BigOperators

set_option autoImplicit false

theorem mme_stothers_phi224_exact_profile_entropy_polynomial_lower
    (N alpha beta gamma delta : ℕ) (hN : 0 < N)
    (hsum : alpha + 2 * beta + gamma + delta = N) :
    Real.exp
        (((2 * N : ℕ) : ℝ) *
          (2 * Real.negMulLog
              ((alpha : ℝ) / ((2 * N : ℕ) : ℝ)) +
            4 * Real.negMulLog
              ((beta : ℝ) / ((2 * N : ℕ) : ℝ)) +
            2 * Real.negMulLog
              ((gamma : ℝ) / ((2 * N : ℕ) : ℝ)) +
            Real.negMulLog
              (((2 * delta : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ)))) ≤
      (6 * (((2 * N + 1 : ℕ) : ℝ))) ^ 9 *
        (Nat.card
          (MME.StothersFourth.Phi224.ExactProfileWord
            N alpha beta gamma delta) : ℝ) := by
  sorry
