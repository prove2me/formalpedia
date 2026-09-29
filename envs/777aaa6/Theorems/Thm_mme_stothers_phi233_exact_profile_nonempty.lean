-- Prove2me | Theorems.Thm_mme_stothers_phi233_exact_profile_nonempty
-- name    : mme_stothers_phi233_exact_profile_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:40:40.05703+00:00
-- url     : https://prove2.me/theorems/38b21ed1-23b6-463a-a05c-28db9862d5a6
-- title:
--   The exact phi_233 joint-profile family is nonempty
-- statement:
--   Let $N,\alpha,\beta,\gamma,\delta$ be nonnegative integers satisfying $2\alpha+\beta+\gamma+\delta=N$. Then there exists a length-$2N$ three-mode address supported on the ten ordered $\varphi_{233}$ types whose joint multiplicity vector is exactly
--
--   $$
--   (\alpha,\beta,\alpha,\gamma,\delta,\delta,\gamma,\alpha,\beta,\alpha).
--   $$
--
--   In particular, its three mode marginals are the prescribed Davie--Stothers marginals, so it is an element of the exact target family $S_0\subseteq S$. This supplies the nonemptiness input needed before the exceptional same-marginal completion family can be pruned by type-2 hashing.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), type-2 setup and Lemma 5.1(v), pp. 359--360 and 366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data
import Theorems.Thm_mme_stothers_phi233_profile_total_and_marginals
import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_nonempty

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_phi233_exact_profile_nonempty
    (N alpha beta gamma delta : ℕ)
    (hsum : 2 * alpha + beta + gamma + delta = N) :
    Nonempty
      (MME.StothersFourth.Phi233.ExactProfileAddress
        N alpha beta gamma delta) := by
  sorry
