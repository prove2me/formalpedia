-- Prove2me | Theorems.Thm_binomial_upper_strict_tail_le_half
-- name    : binomial_upper_strict_tail_le_half
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T13:50:33.436265+00:00
-- url     : https://prove2.me/theorems/05a170da-b044-40bd-b15c-ee3092fe7e91
-- title:
--   The strict binomial upper tail at an integer mean is at most $\tfrac12$
-- statement:
--   Let $X\sim\mathrm{Binomial}(N,p)$ with the inclusion probability fixed at the integer mean $p=m/N$ (where $m\le N$). Then the strict upper tail carries at most half the mass: $$\sum_{k=m+1}^{N}\binom{N}{k}p^k(1-p)^{N-k} \le \tfrac12, \qquad \text{i.e. } \mathbb{P}(X\ge m+1)\le\tfrac12.$$ This is the genuine combinatorial core of the Kaas-Buhrman theorem that the median of a binomial with integer mean equals the mean. Unlike the (false) term-by-term tail comparison, this bound holds for ALL $m\le N$. Combined with the total-probability identity $\sum_{k=0}^N\binom{N}{k}p^k(1-p)^{N-k}=1$ it yields $\mathbb{P}(X\le m)=1-\mathbb{P}(X\ge m+1)\ge\tfrac12$.
-- source:
--   https://doi.org/10.1080/00031305.1980.10483006

import Definitions.Def_matrix_completion_fixed_cardinality
open MatrixCompletion

theorem binomial_upper_strict_tail_le_half (N m : ℕ) (h : m ≤ N) : ∑ k ∈ Finset.Ioo m (N + 1), binomialCardinalityProb N k ((m : ℝ) / (N : ℝ)) ≤ (1 / 2 : ℝ) := by sorry
