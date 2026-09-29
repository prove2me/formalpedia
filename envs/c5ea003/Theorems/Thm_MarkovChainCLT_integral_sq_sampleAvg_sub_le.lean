-- Prove2me | Theorems.Thm_MarkovChainCLT_integral_sq_sampleAvg_sub_le
-- name    : MarkovChainCLT.integral_sq_sampleAvg_sub_le
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T23:31:01.666137+00:00
-- url     : https://prove2.me/theorems/46b3eacd-cb69-44ce-9331-ee6c2bd19a86
-- title:
--   $O(1/n)$ mean-square law of large numbers for a uniformly ergodic chain
-- statement:
--   **A quantitative law of large numbers in $L^2$ for a uniformly ergodic chain.** For a bounded measurable $\varphi$ there is a constant $K$ with
--   $$\mathbb E_\lambda\Bigl[\Bigl(\frac1n\sum_{k<n}\varphi(X_{k+1}) - \mathbb E_\pi\varphi\Bigr)^{\!2}\Bigr] \;\le\; \frac{K}{n} \qquad\text{for all } n\ge1,$$
--   for **every** initial distribution $\lambda$. In particular the sample average converges to $\mathbb E_\pi\varphi$ in $L^2$, hence in probability, at the parametric rate $n^{-1/2}$.
--
--   **No ergodic theorem is used.** The usual route to a law of large numbers for Markov chains is Birkhoff's pointwise ergodic theorem, which needs the ergodicity of the shift on path space. Here the conclusion — convergence in $L^2$ with an explicit rate, which is all a central limit theorem needs — comes from the martingale approximation instead, and the argument is completely elementary once the Poisson equation is available.
--
--   **Proof.** Uniform ergodicity provides a *bounded* solution $g$ of $g - Pg = \varphi - \mathbb E_\pi\varphi$. Applying it at the point $X_{k+1}$ and telescoping,
--   $$\sum_{k<n}\bigl(\varphi(X_{k+1}) - \mathbb E_\pi\varphi\bigr) \;=\; \sum_{k<n}\underbrace{\bigl(g(X_{k+1}) - (Pg)(X_k)\bigr)}_{D_k} \;+\; (Pg)(X_0) - (Pg)(X_n).$$
--   The remainder is bounded by $2\|g\|_\infty$ uniformly, and the martingale differences $D_k$ are orthogonal, so $\mathbb E[(\sum_{k<n}D_k)^2] \le n(2\|g\|_\infty)^2$. Using $(a+b)^2\le 2a^2+2b^2$ and dividing by $n^2$,
--   $$\mathbb E\Bigl[\Bigl(\frac1n\sum_{k<n}(\varphi(X_{k+1}) - \mathbb E_\pi\varphi)\Bigr)^{\!2}\Bigr] \;\le\; \frac{2(2\|g\|_\infty)^2}{n} + \frac{2(2\|g\|_\infty)^2}{n^2} \;\le\; \frac{4(2\|g\|_\infty)^2}{n}.$$
--
--   **Where it is used.** In the central limit theorem for the chain, the martingale CLT requires the quadratic variation $\frac1n\sum_{k<n}D_k^2$ to converge to a constant. Expanding $D_k^2$ produces two terms of the form "bounded function of a single coordinate", to which this lemma applies directly, plus a martingale transform which vanishes by its own variance bound.
-- source:
--   M. I. Gordin and B. A. Lifsic, "The central limit theorem for stationary Markov processes", Soviet Math. Dokl. 19 (1978) 392-394; L. Tierney, "Markov Chains for Exploring Posterior Distributions", Annals of Statistics 22 (1994) 1701-1728; S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 17; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320.

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovIterKernel
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder
  ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

theorem MarkovChainCLT.integral_sq_sampleAvg_sub_le {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (huni : UniformlyErgodic P π) (lam : Measure X) [IsProbabilityMeasure lam]
    (φ : X → ℝ) (hφ : Measurable φ) (B : ℝ) (hB : ∀ x, |φ x| ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n →
      ∫ ω, ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, φ (ω (k + 1)) - ∫ x, φ x ∂π) ^ 2
          ∂(chainMeasure P lam) ≤ K / n := by sorry
