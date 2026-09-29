-- Prove2me | Theorems.Thm_binomial_integer_mean_upper_tail_le_half
-- name    : binomial_integer_mean_upper_tail_le_half
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T15:00:57.389008+00:00
-- url     : https://prove2.me/theorems/39566694-1625-499c-87aa-79600b7e2aeb
-- title:
--   Binomial median at an integer mean: $\Pr[X\ge m+1]\le\tfrac12$
-- statement:
--   **Integer-mean binomial median (upper-tail form).** Let $X \sim \mathrm{Bin}(N, m/N)$ with integer mean $m = Np$ (so $0 \le m < N$). Then the strict upper tail satisfies $$\Pr[X \ge m+1] = \sum_{k=m+1}^{N} \binom{N}{k}\left(\tfrac{m}{N}\right)^{k}\left(1-\tfrac{m}{N}\right)^{N-k} \le \tfrac{1}{2}.$$ Equivalently $\Pr[X \le m] \ge \tfrac12$, i.e. the integer mean $m$ is a median of $\mathrm{Bin}(N, m/N)$. This is the classical fact that a binomial distribution whose mean is an integer has that mean as a median (Kaas-Buhrman 1980; Jogdeo-Samuels 1968; Neumann 1966; Siegel 2001). It is the genuine analytic core of the binomial-median branch. Here $\texttt{binomialCardinalityProb}\ N\ k\ p = \binom{N}{k} p^k (1-p)^{N-k}$ and $\texttt{Finset.Ioo}\ m\ (N{+}1) = \{m{+}1,\dots,N\}$.
-- source:
--   R. Kaas & J. M. Buhrman, Mean, median and mode in binomial distributions, Statistica Neerlandica 34(1):13-18 (1980); K. Jogdeo & S. M. Samuels, Monotone convergence of binomial probabilities and a generalisation of Ramanujan's equation, Ann. Math. Statist. 39:1191-1195 (1968); P. Neumann (1966); A. Siegel, Median Bounds and their Application, J. Algorithms 38:184-236 (2001), Thm 2.2 (self-contained proof via the moustache-CDF Lemma 2.1 + Thm 2.1).

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_matrix_completion_fixed_cardinality
open scoped BigOperators
open Finset
open MatrixCompletion

theorem binomial_integer_mean_upper_tail_le_half (N m : ℕ) (h : m < N) : ∑ k ∈ Finset.Ioo m (N + 1), binomialCardinalityProb N k ((m : ℝ) / (N : ℝ)) ≤ (1 / 2 : ℝ) := by sorry
