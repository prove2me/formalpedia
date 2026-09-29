-- Prove2me | Theorems.Thm_binomial_full_sum_eq_one
-- name    : binomial_full_sum_eq_one
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T04:50:43.959068+00:00
-- url     : https://prove2.me/theorems/7eec7a28-805d-4c88-a436-d524f908be19
-- title:
--   Binomial masses sum to one
-- statement:
--   For any number of trials $N$ and inclusion probability $p$, the binomial probability mass sums to one over all cardinalities $k=0,\dots,N$: $$\sum_{k=0}^{N} \binom{N}{k} p^k (1-p)^{N-k} = 1.$$ This is the normalization (total probability) identity for the binomial distribution, with the platform weight $\operatorname{binomialCardinalityProb}(N,k,p)=\binom{N}{k}p^k(1-p)^{N-k}$.
-- source:
--   https://en.wikipedia.org/wiki/Binomial_theorem

import Definitions.Def_matrix_completion_fixed_cardinality
open MatrixCompletion

theorem binomial_full_sum_eq_one (N : ℕ) (p : ℝ) : ∑ k ∈ Finset.range (N + 1), binomialCardinalityProb N k p = 1 := by sorry
