-- Prove2me | Theorems.Thm_MarkovChainCLT_integral_sq_sum_weighted_mds_le
-- name    : MarkovChainCLT.integral_sq_sum_weighted_mds_le
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T23:25:37.103702+00:00
-- url     : https://prove2.me/theorems/ee4abe82-5901-4004-9f13-9b4b7addc2bb
-- title:
--   Linear variance bound for a predictably weighted martingale transform
-- statement:
--   **A linear variance bound for martingale transforms of a Markov chain.** For bounded measurable $g$ and $u$, set
--   $$D_k \;=\; u(X_k)\,\bigl(g(X_{k+1}) - (Pg)(X_k)\bigr).$$
--   Then under the chain law from any initial distribution,
--   $$\mathbb E\Bigl[\Bigl(\sum_{k<n} D_k\Bigr)^{\!2}\Bigr] \;\le\; n\,\bigl(\|u\|_\infty\,2\|g\|_\infty\bigr)^2 .$$
--
--   **A martingale transform, not just a martingale.** The weight $u(X_k)$ is *predictable*: it is measurable with respect to $\sigma(X_0,\dots,X_k)$, the same $\sigma$-algebra against which the increment $g(X_{k+1}) - (Pg)(X_k)$ has zero conditional mean. Hence $\mathbb E[D_k \mid \sigma(X_0,\dots,X_k)] = u(X_k)\cdot 0 = 0$: multiplying by a predictable factor preserves the martingale-difference property, and with it the orthogonality $\mathbb E[D_jD_k]=0$ for $j\ne k$. Expanding the square leaves only the diagonal, giving the linear-in-$n$ bound. Taking $u \equiv 1$ recovers the plain martingale case.
--
--   **Why the weighted form is needed.** In the central limit theorem for a Markov chain one must control the *quadratic variation* $\frac1n\sum_{k<n} D_k^2$ of the martingale approximation, and expanding
--   $$\bigl(g(X_{k+1}) - (Pg)(X_k)\bigr)^2 \;=\; g(X_{k+1})^2 \;-\; 2\,(Pg)(X_k)\bigl(g(X_{k+1}) - (Pg)(X_k)\bigr) \;-\; (Pg)(X_k)^2$$
--   produces exactly a martingale transform with the predictable weight $u = Pg$, alongside two terms that are functions of a single coordinate. The bound above makes the transform term $O(n)$ in $L^2$, hence $o(n)$ after dividing by $n$, so the quadratic variation converges to a deterministic limit without any appeal to an ergodic theorem.
-- source:
--   P. Hall and C. C. Heyde, Martingale Limit Theory and Its Application, Academic Press 1980, Section 2.3 and Section 3.3; M. I. Gordin and B. A. Lifsic, "The central limit theorem for stationary Markov processes", Soviet Math. Dokl. 19 (1978) 392-394; S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 17.

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovIterKernel
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder
  ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

theorem MarkovChainCLT.integral_sq_sum_weighted_mds_le {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (lam : Measure X) [IsProbabilityMeasure lam]
    (g : X → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ x, |g x| ≤ C)
    (u : X → ℝ) (hu : Measurable u) (K : ℝ) (hK : ∀ x, |u x| ≤ K) (n : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range n, u (ω k) * (g (ω (k + 1)) - ∫ y, g y ∂(P (ω k)))) ^ 2
        ∂(chainMeasure P lam)
      ≤ n * (K * (2 * C)) ^ 2 := by sorry
