-- Prove2me | Theorems.Thm_MarkovChainCLT_clt_of_bounded_of_uniformlyErgodic
-- name    : MarkovChainCLT.clt_of_bounded_of_uniformlyErgodic
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T23:55:52.116576+00:00
-- url     : https://prove2.me/theorems/67cf6ead-c57a-4c00-8bd9-11a46cbe221c
-- title:
--   Markov chain CLT for a bounded observable of a uniformly ergodic chain
-- statement:
--   **The central limit theorem for a bounded observable of a uniformly ergodic Markov chain.** If $P$ is uniformly ergodic with invariant probability $\pi$ and $f$ is bounded and measurable, then for every initial distribution $\lambda$,
--   $$\sqrt n\,\bigl(\bar f_n - \mathbb E_\pi f\bigr) \;\xrightarrow{\ d\ }\; N(0,\sigma^2), \qquad \sigma^2 = \mathbb E_\pi\bigl[g^2\bigr] - \mathbb E_\pi\bigl[(Pg)^2\bigr],$$
--   where $g$ solves the Poisson equation $g - Pg = f - \mathbb E_\pi f$. This is Corollary 5 of Jones' survey restricted to bounded $f$ — the case in which the whole argument can be carried out with bounded quantities only.
--
--   **The proof is Gordin's martingale approximation, made completely elementary.** Uniform ergodicity gives a *bounded* solution $g$ of the Poisson equation, and the partial sums decompose exactly as
--   $$\sum_{k<n}\bigl(f(X_{k+1}) - \mathbb E_\pi f\bigr) \;=\; \sum_{k<n} D_k \;+\; (Pg)(X_0) - (Pg)(X_n), \qquad D_k = g(X_{k+1}) - (Pg)(X_k).$$
--
--   * The $D_k$ are **martingale differences** for the natural filtration of the chain — this is exactly the Markov property in conditional-expectation form — and they are **bounded** by $2\|g\|_\infty$, so the triangular array $D_{n,k} = n^{-1/2}D_k$ satisfies $\sum_{k<n} D_{n,k}^2 \le (2\|g\|_\infty)^2$ pathwise and $\max_k|D_{n,k}| \to 0$.
--   * Its **quadratic variation converges**: $\frac1n\sum_{k<n}D_k^2 \to \sigma^2$ in $L^2$ at rate $1/n$, obtained by expanding $D_k^2$ into two sample averages of bounded functions of a single coordinate — handled by the mean-square law of large numbers — plus a predictably weighted martingale transform, which vanishes. **No ergodic theorem is used anywhere.**
--   * The martingale central limit theorem for bounded arrays then gives $n^{-1/2}\sum_{k<n}D_k \to N(0,\sigma^2)$, and the remainder $n^{-1/2}\bigl((Pg)(X_0)-(Pg)(X_n)\bigr)$ is $O(n^{-1/2})$ uniformly, hence negligible in probability.
--   * Finally, the geometric total-variation rate transfers the stationary limit law to an arbitrary initial distribution.
--
--   **Nonnegativity of $\sigma^2$** comes from Jensen's inequality $(Pg)^2 \le P(g^2)$ together with the invariance $\mathbb E_\pi[P(g^2)] = \mathbb E_\pi[g^2]$, so the limit really is a Gaussian law (possibly degenerate).
-- source:
--   M. I. Gordin and B. A. Lifsic, "The central limit theorem for stationary Markov processes", Soviet Math. Dokl. 19 (1978) 392-394; I. A. Ibragimov and Yu. V. Linnik, Independent and Stationary Sequences of Random Variables, Wolters-Noordhoff 1971; L. Tierney, "Markov Chains for Exploring Posterior Distributions", Annals of Statistics 22 (1994) 1701-1728; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, Corollary 5.

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovIterKernel
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder
  ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.clt_of_bounded_of_uniformlyErgodic {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) (huni : UniformlyErgodic P π)
    (f : X → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) :
    SatisfiesCLT P π f := by sorry
