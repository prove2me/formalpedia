-- Prove2me | Theorems.Thm_mme_stothers_phi233_exact_star_factorization
-- name    : mme_stothers_phi233_exact_star_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:51:24.320575+00:00
-- url     : https://prove2.me/theorems/3d281f28-6d50-4927-9b2f-1a10fdefe750
-- title:
--   Exact fixed-mode star factorization of the phi_233 target family
-- statement:
--   Assume the phi_233 profile parameters satisfy $2\alpha+\beta+\gamma+\delta=N$. For every exact-profile address and every mode, the total number of exact-profile addresses equals the multinomial number of words having the prescribed marginal in that mode times the number of exact-profile addresses containing the fixed word. Thus the target hypergraph is exactly regular, with precisely the same mode-word factor as the full same-marginal ambient hypergraph. This common factor is what permits a global completion ratio to be transferred to a sharp local-degree ratio.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, the exact-profile and same-marginal counts in Lemma 5.1(v), pp. 365--367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_marginal_profile_table
import Theorems.Thm_mme_stothers_phi233_pattern_injective
import Theorems.Thm_mme_stothers_phi233_profile_total_and_marginals
import Theorems.Thm_mme_stothers_phi233_exact_profile_card
import Theorems.Thm_mme_stothers_phi233_fixed_mode_profile_table_fiber_card

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000

theorem mme_stothers_phi233_exact_star_factorization
    (N alpha beta gamma delta : ℕ)
    (hsum : 2 * alpha + beta + gamma + delta = N)
    (a : MME.StothersFourth.Phi233.ExactProfileAddress
      N alpha beta gamma delta) (i : Fin 3) :
    Nat.card
        (MME.StothersFourth.Phi233.ExactProfileAddress
          N alpha beta gamma delta) =
      ((2 * N).factorial /
        ∏ s : Fin 5,
          (MME.StothersFourth.Phi233.marginalMultiplicity
            alpha beta gamma delta i s).factorial) *
        Nat.card
          {b : MME.StothersFourth.Phi233.ExactProfileAddress
              N alpha beta gamma delta // b.1.1 i = a.1.1 i} := by
  sorry
