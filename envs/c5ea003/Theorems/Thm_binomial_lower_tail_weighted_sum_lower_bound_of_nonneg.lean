-- Prove2me | Theorems.Thm_binomial_lower_tail_weighted_sum_lower_bound_of_nonneg
-- name    : binomial_lower_tail_weighted_sum_lower_bound_of_nonneg
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T08:34:52.051155+00:00
-- url     : https://prove2.me/theorems/f4a5a1ee-bda0-4355-bfd3-3abf0732c176
-- statement:
--   This is the corrected weighted lower-tail estimate for the Bernoulli-to-fixed-cardinality transfer.  Let
--
--   $$
--   B_k=inom Nk p^k(1-p)^{N-k}
--   $$
--
--   be the binomial probability weight, and let
--
--   $$
--   L=sum_{k=0}^{m} B_k
--   $$
--
--   be the lower-tail mass.  Assume $0le ple1$, $mle N$, $age0$, every weight value is nonnegative, $f(k)ge0$, and on the lower tail one has $f(k)ge a$ for all $kle m$.  If $Lge1/2$, then the full weighted sum satisfies
--
--   $$
--   sum_{k=0}^{N} B_k f(k) ge rac{a}{2}.
--   $$
--
--   The nonnegativity hypotheses are essential: the deprecated predecessor omitted them, allowing large negative contributions outside the lower tail and therefore was false.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_fixed_cardinality
open MatrixCompletion
open scoped Classical BigOperators

theorem binomial_lower_tail_weighted_sum_lower_bound_of_nonneg
    (N m : ℕ) (p a : ℝ) (f : ℕ → ℝ) :
    0 ≤ p → p ≤ 1 → m ≤ N → 0 ≤ a →
    (∀ k : ℕ, 0 ≤ f k) →
    (∀ k : ℕ, k ≤ m → a ≤ f k) →
    (1 / 2 : ℝ) ≤ binomialLowerTailProb N m p →
    (1 / 2) * a ≤
      ∑ k ∈ Finset.range (N + 1), binomialCardinalityProb N k p * f k := by
  sorry
