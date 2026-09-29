-- Prove2me | Theorems.Thm_MarkovChainCLT_integral_sq_quadVar_sub_le
-- name    : MarkovChainCLT.integral_sq_quadVar_sub_le
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T23:41:42.893536+00:00
-- url     : https://prove2.me/theorems/3ce1924b-8125-4e96-8df6-c10041fd1651
-- title:
--   Mean-square convergence of the quadratic variation, at rate $1/n$
-- statement:
--   **The quadratic variation of the martingale approximation converges, with an $O(1/n)$ rate in mean square.** For a bounded measurable $g$ let $D_k = g(X_{k+1}) - (Pg)(X_k)$. Then for a uniformly ergodic chain, started from **any** initial law,
--   $$\mathbb E\Bigl[\Bigl(\frac1n\sum_{k<n} D_k^2 \;-\; \sigma^2\Bigr)^{\!2}\Bigr] \;\le\; \frac{K}{n}, \qquad \sigma^2 \;=\; \mathbb E_\pi\bigl[g^2\bigr] - \mathbb E_\pi\bigl[(Pg)^2\bigr].$$
--
--   **Why this is the last missing hypothesis of the martingale CLT.** Every martingale central limit theorem needs the conditional (or unconditional) quadratic variation of the array to converge to a constant. For the array $D_{n,k} = n^{-1/2}D_k$ that quantity is exactly $\frac1n\sum_{k<n}D_k^2$, and the statement above gives its convergence in $L^2$, hence in $L^1$ and in probability. The limit $\mathbb E_\pi[g^2] - \mathbb E_\pi[(Pg)^2]$ is the familiar asymptotic variance of the martingale approximation, nonnegative by Jensen's inequality.
--
--   **No ergodic theorem is invoked.** Expanding the square,
--   $$D_k^2 \;=\; g(X_{k+1})^2 \;-\; 2\,(Pg)(X_k)\bigl(g(X_{k+1}) - (Pg)(X_k)\bigr) \;-\; (Pg)(X_k)^2,$$
--   splits the quadratic variation into three pieces of very different nature:
--
--   * $\frac1n\sum_{k<n} g(X_{k+1})^2$ and $\frac1n\sum_{k<n}(Pg)(X_k)^2$ are sample averages of **bounded functions of a single coordinate**, and the mean-square law of large numbers for uniformly ergodic chains gives each an $O(1/n)$ error against its $\pi$-mean. (The second sum is over $X_k$ rather than $X_{k+1}$; shifting the index costs a telescoping remainder $\frac1n\bigl((Pg)(X_0)^2 - (Pg)(X_n)^2\bigr)$, which is $O(1/n)$ uniformly.)
--   * $\frac1n\sum_{k<n}(Pg)(X_k)\bigl(g(X_{k+1}) - (Pg)(X_k)\bigr)$ is a **martingale transform** with the predictable weight $Pg$; its variance bound gives $O(1/n)$ in mean square, so it vanishes.
--
--   Combining the three with $(a+b+c)^2 \le 3(a^2+b^2+c^2)$ gives the stated bound.
-- source:
--   P. Hall and C. C. Heyde, Martingale Limit Theory and Its Application, Academic Press 1980, Ch. 3; M. I. Gordin and B. A. Lifsic, "The central limit theorem for stationary Markov processes", Soviet Math. Dokl. 19 (1978) 392-394; L. Tierney, "Markov Chains for Exploring Posterior Distributions", Annals of Statistics 22 (1994) 1701-1728; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320.

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovIterKernel
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder
  ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

theorem MarkovChainCLT.integral_sq_quadVar_sub_le {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (huni : UniformlyErgodic P π) (lam : Measure X) [IsProbabilityMeasure lam]
    (g : X → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ x, |g x| ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n →
      ∫ ω, ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (g (ω (k + 1)) - ∫ y, g y ∂(P (ω k))) ^ 2
            - (∫ x, (g x) ^ 2 ∂π - ∫ x, (∫ y, g y ∂(P x)) ^ 2 ∂π)) ^ 2
          ∂(chainMeasure P lam) ≤ K / n := by sorry
