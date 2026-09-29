-- Prove2me | Theorems.Thm_mme_stothers_phi134_behrend_prime_of_cyclic_degree
-- name    : mme_stothers_phi134_behrend_prime_of_cyclic_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:27:32.28997+00:00
-- url     : https://prove2.me/theorems/df3b65bf-93e7-400d-8c43-d312c4408b5e
-- title:
--   Prime and progression-free labels for the Phi134 cyclic degree
-- statement:
--   Let $D=D_0D_1D_2$ be the sharp cyclic same-mode degree of an integral symmetric $\phi_{134}$ profile of length $2N$.  There are a prime $p\geq7$ and a progression-free label set $S\subseteq\mathbb Z/p\mathbb Z$ such that
--
--   $$6D\leq|S|,\qquad p\leq D\exp\bigl(2000\sqrt{12N+1}\bigr).$$
--
--   Progression-free means that $x+y=2z$ for three labels in $S$ forces $x=z=y$.  This is the quantitative prime--Behrend input for the type-2 Phi134 affine hash, expressed using the same exact degree as its uniform cyclic fibers.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh Section A 143(2), 2013, Lemma 3.3 and Lemma 5.1(iii), pp. 359–365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. Quantitative modulus bound supplied by the proved theorem mme_prime_behrend_dominates_bounded_collision_degree.

import Definitions.Def_mme_stothers_phi134_cyclic_hash_data

open MME BigOperators
open MME.StothersFourth.Phi134

set_option autoImplicit false

theorem mme_stothers_phi134_behrend_prime_of_cyclic_degree
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
    ∃ p : ℕ, Nat.Prime p ∧ 7 ≤ p ∧
      ∃ S : Finset (ZMod p),
        (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
          x + y = 2 * z → x = z ∧ z = y) ∧
        6 * (D 0 * (D 1 * D 2) : ℝ) ≤ S.card ∧
        (p : ℝ) ≤ (D 0 * (D 1 * D 2) : ℝ) *
          Real.exp (2000 * Real.sqrt ((12 * N + 1 : ℕ) : ℝ)) := by
  sorry
