-- Prove2me | Theorems.Thm_mme_stothers_phi233_address_star_ratio
-- name    : mme_stothers_phi233_address_star_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:57:02.840309+00:00
-- url     : https://prove2.me/theorems/24b02fea-ad1b-4020-b248-87030cd6c661
-- title:
--   Lossless fixed-mode degree ratio for phi_233 completions
-- statement:
--   Assume $2\alpha+\beta+\gamma+\delta=N$, and suppose the full same-marginal completion family has size at most $R$ times the exact-profile family. For any exact-profile address and any one of the three modes, the number of ambient completions containing its fixed mode word is at most $R$ times the number of exact-profile completions containing that word. The result transfers the global entropy bound to the local collision degree with no additional loss, which is the critical estimate for the type-2 hashing argument.
-- source:
--   Derived from the regular same-marginal and exact-profile counts underlying A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 5.1(v).

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_marginal_profile_table
import Theorems.Thm_mme_stothers_phi233_marginal_star_factorization
import Theorems.Thm_mme_stothers_phi233_exact_star_factorization

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000

theorem mme_stothers_phi233_address_star_ratio
    (N alpha beta gamma delta : ℕ)
    (hsum : 2 * alpha + beta + gamma + delta = N)
    (a : MME.StothersFourth.Phi233.ExactProfileAddress
      N alpha beta gamma delta) (i : Fin 3) (R : ℝ)
    (hratio :
      (Nat.card
          (MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta) : ℝ) ≤
        R *
          (Nat.card
            (MME.StothersFourth.Phi233.ExactProfileAddress
              N alpha beta gamma delta) : ℝ)) :
    (Nat.card
        {b : MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta // b.1 i = a.1.1 i} : ℝ) ≤
      R *
        (Nat.card
          {b : MME.StothersFourth.Phi233.ExactProfileAddress
              N alpha beta gamma delta // b.1.1 i = a.1.1 i} : ℝ) := by
  sorry
