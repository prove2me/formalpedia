-- Prove2me | Theorems.Thm_mme_stothers_phi233_ambient_star_crude_bounds
-- name    : mme_stothers_phi233_ambient_star_crude_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-04T05:55:26.164109+00:00
-- url     : https://prove2.me/theorems/c47ae50a-7e85-48f5-87c1-9941ae45c72d
-- title:
--   Crude ambient star bounds for cyclic phi_233
-- statement:
--   Fix a realized exact $\varphi_{233}$ profile of length $2N$ and an exact address $a$. Let $D$ be the product of the three ambient fixed-mode star cardinalities at $a$. Then
--
--   $$
--   1\le D\le 5^{18N}.
--   $$
--
--   The lower bound records that each mode star contains at least the address itself. The upper bound compares each mode star with the unrestricted space of length-$2N$ three-mode words over a five-letter alphabet and multiplies the three resulting $5^{6N}$ estimates. This polynomial-in-exponential crude degree is the exact input required by the bounded-degree Behrend/prime selection lemma after the scale substitution $N\mapsto 18N$.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, the phi_233 ambient completion counts underlying Lemma 5.1(v).

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_phi233_ambient_star_crude_bounds
    (N alpha beta gamma delta : ℕ)
    (a : MME.StothersFourth.Phi233.ExactProfileAddress
      N alpha beta gamma delta) :
    let D := ∏ l : Fin 3,
      Nat.card
        {b : MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta // b.1 l = a.1.1 l}
    1 ≤ D ∧ D ≤ 5 ^ (18 * N) := by
  sorry
