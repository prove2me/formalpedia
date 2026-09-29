-- Prove2me | Theorems.Thm_mme_prime_behrend_dominates_bounded_collision_degree
-- name    : mme_prime_behrend_dominates_bounded_collision_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T21:21:30.655966+00:00
-- url     : https://prove2.me/theorems/a64b7703-0a6b-4843-8b02-7bb364a8e403
-- title:
--   A prime Behrend hash set pays every collision degree bounded by $5^N$
-- statement:
--   For all integers $N,D$ with $1\le D\le5^N$, there are a prime $p\ge5$ and a three-term-progression-free set $S$ in the lower half of $\mathbb Z/p\mathbb Z$ such that
--
--   $$
--   |S|\ge6D,\qquad p\le D\exp\bigl(2000\sqrt{N+1}\bigr).
--   $$
--
--   The cardinality lower bound pays the three directed mode-collision budgets with a factor-two reserve, while the modulus bound is subexponential relative to $D$ on the square-root scale. This packages the exact prime and Behrend choices needed in the outer Coppersmith--Winograd $2.376$ pruning argument.
-- source:
--   Explicit Behrend density plus Bertrand's postulate, assembled for the affine-hash collision deletion of D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Theorems.Thm_mme_behrend_bounded_degree_scale
import Theorems.Thm_mme_prime_half_modulus_behrend

theorem mme_prime_behrend_dominates_bounded_collision_degree
    (N D : ℕ) (hD1 : 1 ≤ D) (hD5 : D ≤ 5 ^ N) :
    ∃ p : ℕ, Nat.Prime p ∧ 5 ≤ p ∧
      ∃ S : Finset ℕ,
        S ⊆ Finset.range (p / 2) ∧
        ThreeAPFree (S : Set ℕ) ∧
        (6 * D : ℝ) ≤ (S.card : ℝ) ∧
        (p : ℝ) ≤ (D : ℝ) *
          Real.exp (2000 * Real.sqrt (((N + 1 : ℕ) : ℝ))) := by
  sorry
