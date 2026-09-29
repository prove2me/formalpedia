-- Prove2me | Theorems.Thm_mme_stothers_phi233_exact_profile_card
-- name    : mme_stothers_phi233_exact_profile_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:01:03.915282+00:00
-- url     : https://prove2.me/theorems/42f1cace-b7a8-432d-91d8-bd14c2e42f4b
-- title:
--   Exact multinomial cardinality of the phi_233 target family
-- statement:
--   Let $2\alpha+\beta+\gamma+\delta=N$, and let $S_0$ be the length-$2N$ target family whose ten ordered $\varphi_{233}$ joint types have multiplicities
--
--   $$
--   (\alpha,\beta,\alpha,\gamma,\delta,\delta,\gamma,\alpha,\beta,\alpha).
--   $$
--
--   Then its cardinality is the corresponding multinomial coefficient:
--
--   $$
--   |S_0|=\frac{(2N)!}{\alpha!^4\,\beta!^2\,\gamma!^2\,\delta!^2}
--         =\frac{(2N)!}{\prod_{r=0}^{9}m_r!}.
--   $$
--
--   This is the exact numerator in the exceptional type-2 target-versus-ambient counting argument for $\varphi_{233}$.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Equation (3.6) and Lemma 5.1(v), pp. 360 and 366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data
import Theorems.Thm_mme_stothers_phi233_profile_total_and_marginals
import Theorems.Thm_mme_stothers_phi233_pattern_injective
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem mme_stothers_phi233_exact_profile_card
    (N alpha beta gamma delta : ℕ)
    (hsum : 2 * alpha + beta + gamma + delta = N) :
    Nat.card
        (MME.StothersFourth.Phi233.ExactProfileAddress
          N alpha beta gamma delta) =
      (2 * N).factorial /
        ∏ r : Fin 10,
          (MME.StothersFourth.Phi233.profileMultiplicity
            alpha beta gamma delta r).factorial := by
  sorry
