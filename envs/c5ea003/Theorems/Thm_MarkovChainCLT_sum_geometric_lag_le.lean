-- Prove2me | Theorems.Thm_MarkovChainCLT_sum_geometric_lag_le
-- name    : MarkovChainCLT.sum_geometric_lag_le
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-16T00:38:43.042914+00:00
-- url     : https://prove2.me/theorems/a7bb408d-8b0c-412c-bd68-cecf7a3d6400
-- title:
--   A geometric lag weight sums to $O(N)$ regardless of the horizon
-- statement:
--   **A lag sum of a block-geometric weight is bounded uniformly in $n$.** For every $j < n$,
--   $$\sum_{k<n} 2^{-\lfloor |j-k|/N\rfloor} \;\le\; 4N .$$
--   The bound does **not** grow with $n$: although the sum has $n$ terms, the weight decays geometrically in the lag $|j-k|$, so only $O(N)$ of the mass survives.
--
--   **Where it is used.** For a uniformly ergodic Markov chain the autocovariance obeys $|\mathbb E[r(X_j)r(X_k)]| \le 2^{-\lfloor|j-k|/N\rfloor}\|r\|_{L^2(\pi)}^2$. Expanding the square of a partial sum,
--   $$\operatorname{Var}\Bigl(\sum_{k<n}r(X_k)\Bigr) \;=\; \sum_{j<n}\sum_{k<n}\mathbb E[r(X_j)r(X_k)] \;\le\; \|r\|_{L^2(\pi)}^2\sum_{j<n}\sum_{k<n}2^{-\lfloor|j-k|/N\rfloor} \;\le\; 4N\,n\,\|r\|_{L^2(\pi)}^2 .$$
--   This is exactly the $O(n)$ variance bound — with a constant proportional to $\|r\|_{L^2}^2$ rather than $\|r\|_\infty^2$ — that controls the truncation error when the Markov chain central limit theorem is extended from bounded to square-integrable observables.
--
--   **Proof.** Two steps.
--
--   *The one-sided sum.* Grouping the lags into blocks of length $N$, on which $\lfloor d/N\rfloor$ is constant,
--   $$\sum_{d<qN} 2^{-\lfloor d/N\rfloor} \;=\; \sum_{p<q} N\,2^{-p} \;\le\; 2N\bigl(1-2^{-q}\bigr),$$
--   an induction on $q$ whose step uses $\lfloor (pN+i)/N\rfloor = p$ for $i<N$. Since $m \le mN$ when $N\ge1$ and all terms are nonnegative, $\sum_{d<m}2^{-\lfloor d/N\rfloor} \le 2N$ for every $m$.
--
--   *The two-sided sum.* Split $\{k<n\}$ at $j$. On $\{k\le j\}$ the lag is $j-k$ and $k\mapsto j-k$ is injective with image inside $\{0,\dots,n-1\}$ (using $j<n$); on $\{k>j\}$ the lag is $k-j$ and $k\mapsto k-j$ is injective with image inside $\{0,\dots,n-1\}$ as well. Each half is therefore bounded by the one-sided sum $\le 2N$, giving $4N$ in total.
-- source:
--   I. A. Ibragimov and Yu. V. Linnik, Independent and Stationary Sequences of Random Variables, Wolters-Noordhoff 1971, Ch. 18; P. Billingsley, Convergence of Probability Measures, 2nd ed., Wiley 1999, Section 19; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320.

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic

open Finset

theorem MarkovChainCLT.sum_geometric_lag_le (N : ℕ) (hN : 1 ≤ N) (n j : ℕ) (hj : j < n) :
    ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ ((max j k - min j k) / N) ≤ 4 * N := by sorry
