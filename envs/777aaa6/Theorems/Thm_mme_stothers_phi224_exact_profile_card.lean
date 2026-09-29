-- Prove2me | Theorems.Thm_mme_stothers_phi224_exact_profile_card
-- name    : mme_stothers_phi224_exact_profile_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T09:29:14.114644+00:00
-- url     : https://prove2.me/theorems/17c69bec-c477-485b-91d9-adf5ea3dae57
-- title:
--   Exact multinomial count of phi_224 symmetric profiles
-- statement:
--   Let $\alpha,\beta,\gamma,\delta$ be nonnegative integers with $\alpha+2\beta+\gamma+\delta=N$. A length-$2N$ exact $\varphi_{224}$ profile word has multiplicity vector
--
--   $$
--   (\alpha,\beta,\gamma,\beta,2\delta,\beta,\gamma,\beta,\alpha).
--   $$
--
--   The number of such words is exactly
--
--   $$
--   \frac{(2N)!}{\prod_{r=0}^{8}m_r!}.
--   $$
--
--   This is the target-family cardinality in the numerator of the finite type-2 hashing estimate for Davie--Stothers Lemma 5.1(iv).
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), the type-2 counting lemma and Lemma 5.1(iv), pp. 359--360 and 365--366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi224_profile_data
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card

open BigOperators

set_option autoImplicit false

theorem mme_stothers_phi224_exact_profile_card
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + 2 * beta + gamma + delta = N) :
    Nat.card
        (MME.StothersFourth.Phi224.ExactProfileWord
          N alpha beta gamma delta) =
      (2 * N).factorial /
        ∏ r : Fin 9,
          (MME.StothersFourth.Phi224.profileMultiplicity
            alpha beta gamma delta r).factorial := by
  sorry
