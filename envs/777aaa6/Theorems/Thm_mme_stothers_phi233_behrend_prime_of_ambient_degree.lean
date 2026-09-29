-- Prove2me | Theorems.Thm_mme_stothers_phi233_behrend_prime_of_ambient_degree
-- name    : mme_stothers_phi233_behrend_prime_of_ambient_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T05:58:27.430078+00:00
-- url     : https://prove2.me/theorems/6fe50719-d355-43cb-8494-48ef44a275a2
-- title:
--   Behrend prime selection for cyclic phi_233 ambient degree
-- statement:
--   Fix a realized exact $\varphi_{233}$ profile of length $2N$ and an exact address $a$, and let $D$ be the product of the three ambient fixed-mode stars at $a$. There exist a prime $p\ge7$ and a three-AP-free set $S\subseteq\mathbb F_p$ such that
--
--   $$
--   |S|\ge6D
--   \qquad\text{and}\qquad
--   p\le D\,\exp\bigl(2000\sqrt{18N+1}\bigr).
--   $$
--
--   The construction applies the bounded-degree Behrend lemma at scale $18N$ to the crude ambient bound $D\le5^{18N}$, then casts the half-modulus integer labels into $\mathbb F_p$. This is the exact prime/set package consumed by the actual-degree isolated extraction.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Sections 3 and 5; Behrend progression-free sets as used in the laser method.

import Definitions.Def_mme_stothers_phi233_profile_data
import Theorems.Thm_mme_stothers_phi233_ambient_star_crude_bounds
import Theorems.Thm_mme_prime_behrend_dominates_bounded_collision_degree
import Theorems.Thm_mme_stothers_phi233_lower_half_cast_label_package

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_phi233_behrend_prime_of_ambient_degree
    (N alpha beta gamma delta : ℕ)
    (a : MME.StothersFourth.Phi233.ExactProfileAddress N alpha beta gamma delta) :
    ∃ p : ℕ, Nat.Prime p ∧ 7 ≤ p ∧
      ∃ S : Finset (ZMod p),
        (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
          x + y = 2 * z → x = z ∧ z = y) ∧
        6 *
            ((∏ l : Fin 3,
              Nat.card
                {b : MME.StothersFourth.Phi233.MarginalAddress
                    N alpha beta gamma delta //
                  b.1 l = a.1.1 l}) : ℝ) ≤
          (S.card : ℝ) ∧
        (p : ℝ) ≤
          ((∏ l : Fin 3,
              Nat.card
                {b : MME.StothersFourth.Phi233.MarginalAddress
                    N alpha beta gamma delta //
                  b.1 l = a.1.1 l}) : ℝ) *
            Real.exp (2000 * Real.sqrt (((18 * N + 1 : ℕ) : ℝ))) := by
  sorry
