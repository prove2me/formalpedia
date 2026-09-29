-- Prove2me | Theorems.Thm_erdos_arithmetic_progressions
-- name    : erdos_arithmetic_progressions
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T19:12:35.153187+00:00
-- url     : https://prove2.me/theorems/9b48e80d-26af-4851-9e8e-6fafaee35f5e
-- statement:
--   **Erdős Conjecture on Arithmetic Progressions**: If $A$ is a set of positive integers such that $\sum_{n \in A} \frac{1}{n} = \infty$ (the reciprocal series diverges), then $A$ contains arithmetic progressions of every finite length.
--
--   Proposed by Paul Erdős (1936). The Green-Tao theorem (2004) proves this for $A = $ the primes. For general sets with divergent reciprocal sums, it remains open. Settles the case $k=3$ for sets of positive density (van der Waerden's theorem handles the density case). The prize offered by Erdős for this conjecture was \$3000.
--
--   **Source**: Erdős, P. (1936). On the representation of large integers as sums of distinct summands taken from a fixed set. Acta Arithmetica 2, 283–292. Also: Erdős, P. (1963). Problems in combinatorial number theory I. Studies in Pure Math. (Presented to Richard Rado).
-- source:
--   https://en.wikipedia.org/wiki/Erd%C5%91s_conjecture_on_arithmetic_progressions

import Mathlib

theorem erdos_arithmetic_progressions (A : Set ℕ) [DecidablePred (· ∈ A)]
    (hA_pos : ∀ n ∈ A, 0 < n)
    (hA_div : ∀ M : ℝ, ∃ N : ℕ, M ≤
      ∑ n ∈ (Finset.Icc 1 N).filter (· ∈ A), (1 : ℝ) / (n : ℝ)) :
    ∀ k : ℕ, ∃ a d : ℕ, 0 < d ∧ ∀ i < k, (a + i * d) ∈ A := by
  sorry
