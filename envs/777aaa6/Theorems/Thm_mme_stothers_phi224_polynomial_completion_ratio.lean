-- Prove2me | Theorems.Thm_mme_stothers_phi224_polynomial_completion_ratio
-- name    : mme_stothers_phi224_polynomial_completion_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:38:31.3633+00:00
-- url     : https://prove2.me/theorems/70a23954-88a1-4895-8e66-b32d4a3c485d
-- title:
--   Explicit polynomial completion ratio for phi_224 profiles
-- statement:
--   Let $N>0$ and let $\alpha+2\beta+\gamma+\delta=N$. Write $S$ for the family of all length-$2N$ words in the nine fine $\varphi_{224}$ types with the prescribed three projected marginals, and write $S_0$ for the distinguished exact-profile family with multiplicities
--
--   $$
--   (\alpha,\beta,\gamma,\beta,2\delta,\beta,\gamma,\beta,\alpha).
--   $$
--
--   Then
--
--   $$
--   |S|\leq (2N+1)^9\bigl(6(2N+1)\bigr)^9|S_0|.
--   $$
--
--   Thus every same-marginal completion is controlled by the exact symmetric family up to an explicit degree-$18$ polynomial factor. This is the finite completion-ratio input used to bound the relative collision degree in the type-2 affine-hashing extraction.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), equations (3.5)--(3.6) and Lemma 5.1(iv), pp. 359--360 and 365--366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi224_profile_data
import Theorems.Thm_mme_stothers_phi224_marginal_profile_entropy_upper
import Theorems.Thm_mme_stothers_phi224_exact_profile_entropy_polynomial_lower

set_option autoImplicit false

theorem mme_stothers_phi224_polynomial_completion_ratio
    (N alpha beta gamma delta : ℕ) (hN : 0 < N)
    (hsum : alpha + 2 * beta + gamma + delta = N) :
    (Nat.card
        (MME.StothersFourth.Phi224.MarginalProfileWord
          N alpha beta gamma delta) : ℝ) ≤
      ((((2 * N + 1 : ℕ) : ℝ)) ^ 9 *
        (6 * (((2 * N + 1 : ℕ) : ℝ))) ^ 9) *
        (Nat.card
          (MME.StothersFourth.Phi224.ExactProfileWord
            N alpha beta gamma delta) : ℝ) := by
  sorry
