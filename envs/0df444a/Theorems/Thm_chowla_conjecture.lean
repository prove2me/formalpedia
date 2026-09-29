-- Prove2me | Theorems.Thm_chowla_conjecture
-- name    : chowla_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T19:07:37.002759+00:00
-- url     : https://prove2.me/theorems/bcec3639-382d-43db-9f69-02aa81e168a6
-- statement:
--   **Chowla's Conjecture** (simplest case): The Liouville function $\lambda(n) = (-1)^{\Omega(n)}$ (where $\Omega(n)$ is the number of prime factors with multiplicity) is asymptotically uncorrelated with itself at any positive shift. The simplest case states:
--
--   $$\frac{1}{N} \sum_{n=1}^{N} \lambda(n) \lambda(n+1) \to 0 \quad \text{as } N \to \infty.$$
--
--   The full conjecture (for all $k$-tuples of distinct shifts) implies the prime number theorem in arithmetic progressions and the Bateman-Horn conjecture. The $k=1$ case ($\frac{1}{N}\sum \lambda(n) \to 0$) is equivalent to the prime number theorem. The $k=2$ case above remains open, though Tao (2015) proved a logarithmic version.
--
--   **Source**: Chowla, S. (1965). The Riemann Hypothesis and Hilbert's Tenth Problem. Gordon and Breach, New York. Also: Tao, T. (2015). The Chowla conjecture and the Sarnak conjecture. arXiv:1508.00265.
-- source:
--   https://en.wikipedia.org/wiki/Chowla_conjecture

import Mathlib
open scoped ArithmeticFunction.Omega

theorem chowla_conjecture :
    Filter.Tendsto (fun N : ℕ =>
      (1 : ℝ) / N * ∑ n ∈ Finset.range N,
        ((-1 : ℝ) ^ (ArithmeticFunction.cardFactors n) *
         (-1 : ℝ) ^ (ArithmeticFunction.cardFactors (n + 1))))
      Filter.atTop (nhds 0) := by
  sorry
