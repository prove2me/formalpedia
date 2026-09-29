-- Prove2me | Theorems.Thm_mme_stothers_phi233_profile_total_and_marginals
-- name    : mme_stothers_phi233_profile_total_and_marginals
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:33:42.871309+00:00
-- url     : https://prove2.me/theorems/75762a6c-e8d4-425d-a37e-9096bb3574ec
-- title:
--   Exact total and three marginals of the phi_233 joint profile
-- statement:
--   Let $\alpha,\beta,\gamma,\delta$ be nonnegative integers with $2\alpha+\beta+\gamma+\delta=N$. Assign the ten ordered $\varphi_{233}$ fine types the multiplicities $$(\alpha,\beta,\alpha,\gamma,\delta,\delta,\gamma,\alpha,\beta,\alpha).$$ Their total is exactly $2N$. Moreover, summing these joint multiplicities over the types having a specified grade in a specified mode gives exactly the three marginal vectors printed in Lemma 5.1(v): $$(2\alpha+\beta,2\gamma+2\delta,2\alpha+\beta,0,0)$$ in the first mode and $$(\alpha+\gamma,\alpha+\beta+\delta,\alpha+\beta+\delta,\alpha+\gamma,0)$$ in each of the other two modes. This verifies that the exact joint-profile family is a subset of the same-marginal completion family used in the type-2 extraction.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(v), p. 366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_phi233_profile_total_and_marginals
    (N alpha beta gamma delta : ℕ)
    (hsum : 2 * alpha + beta + gamma + delta = N) :
    (∑ r : Fin 10,
        MME.StothersFourth.Phi233.profileMultiplicity
          alpha beta gamma delta r) = 2 * N ∧
      ∀ i : Fin 3, ∀ k : Fin 5,
        (∑ r : Fin 10,
          if MME.StothersFourth.Phi233.pattern r i = k then
            MME.StothersFourth.Phi233.profileMultiplicity
              alpha beta gamma delta r
          else 0) =
        MME.StothersFourth.Phi233.marginalMultiplicity
          alpha beta gamma delta i k := by
  sorry
