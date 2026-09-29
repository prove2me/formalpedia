-- Prove2me | Theorems.Thm_mme_stothers_phi233_cyclic_star_ratio
-- name    : mme_stothers_phi233_cyclic_star_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-03T00:07:22.95749+00:00
-- url     : https://prove2.me/theorems/5d5c1fe8-0d79-4900-8dd6-267497cc59c1
-- title:
--   Cubic cyclic degree ratio from phi_233 completion counts
-- statement:
--   Assume the phi_233 profile is valid and the same-marginal completion family has cardinality at most $R$ times that of the exact-profile family, with $R\geq0$. Fix any exact address. The product of its three ambient fixed-word star sizes is then at most $R^3$ times the product of its three exact fixed-word star sizes. Since a cyclic vertex fixes one ordinary word from each of the three modes, this is precisely the cubic local-degree loss required for cyclic type-2 extraction.
-- source:
--   The cyclic-product completion estimate implicit in A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 5.

import Mathlib.Tactic
import Theorems.Thm_mme_stothers_phi233_address_star_ratio

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_phi233_cyclic_star_ratio
    (N alpha beta gamma delta : ℕ)
    (hsum : 2 * alpha + beta + gamma + delta = N)
    (a : MME.StothersFourth.Phi233.ExactProfileAddress
      N alpha beta gamma delta) (R : ℝ) (hR : 0 ≤ R)
    (hratio :
      (Nat.card
          (MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta) : ℝ) ≤
        R *
          (Nat.card
            (MME.StothersFourth.Phi233.ExactProfileAddress
              N alpha beta gamma delta) : ℝ)) :
    ((∏ l : Fin 3,
        Nat.card
          {b : MME.StothersFourth.Phi233.MarginalAddress
              N alpha beta gamma delta // b.1 l = a.1.1 l}) : ℝ) ≤
      R ^ 3 *
        ((∏ l : Fin 3,
          Nat.card
            {b : MME.StothersFourth.Phi233.ExactProfileAddress
                N alpha beta gamma delta // b.1.1 l = a.1.1 l}) : ℝ) := by
  sorry
