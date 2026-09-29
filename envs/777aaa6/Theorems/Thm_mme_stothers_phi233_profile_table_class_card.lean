-- Prove2me | Theorems.Thm_mme_stothers_phi233_profile_table_class_card
-- name    : mme_stothers_phi233_profile_table_class_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:40:02.856751+00:00
-- url     : https://prove2.me/theorems/3b46f092-f673-4670-a720-e7f16dd95ecc
-- title:
--   Exact cardinality of a phi_233 joint-profile stratum
-- statement:
--   Let $k=(k_0,\ldots,k_9)$ be a nonnegative joint table on the ten supported $\varphi_{233}$ patterns, with total mass $2N$ and all three projections equal to the prescribed five-grade marginals. Then the number of same-marginal addresses whose joint profile is exactly $k$ is the multinomial coefficient
--
--   $$
--   \frac{(2N)!}{\prod_{r=0}^{9}k_r!}.
--   $$
--
--   This stratifies the full same-marginal completion family by compatible joint profiles. Together with the fixed-mode conditional count, it gives the exact regularity relation that transfers total entropy bounds to local mode-degree bounds.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, multinomial profile counts in Lemma 3.3 and the phi_233 profile in Lemma 5.1(v), pp. 356--361 and 365--367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_marginal_profile_table
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card
import Theorems.Thm_mme_stothers_phi233_pattern_injective

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem mme_stothers_phi233_profile_table_class_card
    (N alpha beta gamma delta : ℕ) (k : Fin 10 → ℕ)
    (hkTotal : (∑ r : Fin 10, k r) = 2 * N)
    (hkMarginal : ∀ l : Fin 3, ∀ s : Fin 5,
      (∑ r : {r : Fin 10 //
          MME.StothersFourth.Phi233.pattern r l = s}, k r.1) =
        MME.StothersFourth.Phi233.marginalMultiplicity
          alpha beta gamma delta l s) :
    Nat.card
        {b : MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta //
          MME.StothersFourth.Phi233.marginalProfileTable b = k} =
      (2 * N).factorial / ∏ r : Fin 10, (k r).factorial := by
  sorry
