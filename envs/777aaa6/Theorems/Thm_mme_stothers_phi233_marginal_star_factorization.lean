-- Prove2me | Theorems.Thm_mme_stothers_phi233_marginal_star_factorization
-- name    : mme_stothers_phi233_marginal_star_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:47:58.812783+00:00
-- url     : https://prove2.me/theorems/f28e9fb7-2d20-4d68-a3a8-eb596d9a4a7d
-- title:
--   Exact fixed-mode star factorization of the phi_233 ambient family
-- statement:
--   For every realized mode word in the same-marginal phi_233 ambient family, the whole ambient family has cardinality equal to the multinomial number of possible words in that mode times the size of the star fixing that word. In particular, the ambient hypergraph is exactly regular in each of its three modes. This converts global ambient-cardinality estimates into the local mode-degree estimates needed by the hashing and pruning argument, without losing an exponential factor.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, the phi_233 same-marginal completion counts underlying Lemma 5.1(v), pp. 365--367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_marginal_profile_table
import Theorems.Thm_mme_stothers_phi233_fixed_mode_profile_table_fiber_card
import Theorems.Thm_mme_stothers_phi233_profile_table_class_card
import Theorems.Thm_mme_stothers_phi233_marginal_profile_table_constraints

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000

theorem mme_stothers_phi233_marginal_star_factorization
    (N alpha beta gamma delta : ℕ)
    (a : MME.StothersFourth.Phi233.MarginalAddress
      N alpha beta gamma delta) (i : Fin 3) :
    Nat.card
        (MME.StothersFourth.Phi233.MarginalAddress
          N alpha beta gamma delta) =
      ((2 * N).factorial /
        ∏ s : Fin 5,
          (MME.StothersFourth.Phi233.marginalMultiplicity
            alpha beta gamma delta i s).factorial) *
        Nat.card
          {b : MME.StothersFourth.Phi233.MarginalAddress
              N alpha beta gamma delta // b.1 i = a.1 i} := by
  sorry
