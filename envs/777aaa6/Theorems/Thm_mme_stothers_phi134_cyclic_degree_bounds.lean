-- Prove2me | Theorems.Thm_mme_stothers_phi134_cyclic_degree_bounds
-- name    : mme_stothers_phi134_cyclic_degree_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:25:27.31226+00:00
-- url     : https://prove2.me/theorems/e9b2de9b-c7ad-4a00-a651-bc80a2fa6f4b
-- title:
--   Phi134 cyclic degree lies in the prime-selector envelope
-- statement:
--   For every integral symmetric exact $\phi_{134}$ profile of length $2N$, let $D=D_0D_1D_2$ be its sharp cyclic same-mode factorial degree.  Then
--
--   $$1\leq D\leq5^{12N}.$$
--
--   The lower bound records that a same-mode fiber contains its base edge.  The upper bound places the collision degree in exactly the exponential envelope required to invoke the dimension-$12N$ prime--Behrend selection theorem.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh Section A 143(2), 2013, Lemma 3.3 and Lemma 5.1(iii), pp. 359–365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. Prime-envelope constants follow the existing formal theorem mme_prime_behrend_dominates_bounded_collision_degree.

import Mathlib.Data.Nat.Choose.Multinomial
import Definitions.Def_mme_stothers_phi134_cyclic_hash_data

open BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false

theorem mme_stothers_phi134_cyclic_degree_bounds
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N) :
    let D := fun t : Fin 3 ↦
      ∏ s : Fin 5,
        (MME.StothersFourth.Phi134.marginalMultiplicity
          N alpha beta gamma delta t s).factorial /
          ∏ r : {r : Fin 8 //
              MME.StothersFourth.Phi134.pattern r t = s},
            (MME.StothersFourth.Phi134.profileMultiplicity
              alpha beta gamma delta r.1).factorial
    1 ≤ D 0 * (D 1 * D 2) ∧
      D 0 * (D 1 * D 2) ≤ 5 ^ (12 * N) := by
  sorry
