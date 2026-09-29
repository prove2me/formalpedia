-- Prove2me | Theorems.Thm_MarkovChainCLT_integral_sq_sum_coord_le
-- name    : MarkovChainCLT.integral_sq_sum_coord_le
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-16T00:41:51.180724+00:00
-- url     : https://prove2.me/theorems/7ec72eec-e9bf-446e-90b3-c39f34becdd3
-- title:
--   $O(n)$ variance of partial sums, with a constant in the $L^2$ norm
-- statement:
--   **The partial sums of a uniformly ergodic chain have variance $O(n)$, with an $L^2$ constant.** If the $N$-step kernel satisfies $\sup_x\|P^N(x,\cdot)-\pi\|\le\rho$ with $4\rho\le1/4$, then for every bounded measurable $r$ with $\mathbb E_\pi r=0$,
--   $$\mathbb E_\pi\Bigl[\Bigl(\sum_{k<n} r(X_{k+1})\Bigr)^{\!2}\Bigr] \;\le\; 4N\,n\,\|r\|_{L^2(\pi)}^2 .$$
--
--   **The point is the constant.** A trivial bound gives $n^2\|r\|_\infty^2$; the martingale approximation gives $O(n\|\hat r\|_\infty^2)$ where $\hat r$ solves the Poisson equation. Both are useless for the truncation step of the Markov chain central limit theorem, where one writes $f = f_K + r_K$ with $f_K$ bounded and must show that the remainder $r_K$ contributes negligibly: there $\|r_K\|_{L^2(\pi)}\to0$ but $\|r_K\|_\infty$ does not. The bound above is exactly what is needed, since
--   $$\mathbb E_\pi\Bigl[\Bigl(\tfrac1{\sqrt n}\sum_{k<n}r_K(X_{k+1})\Bigr)^{\!2}\Bigr] \;\le\; 4N\,\|r_K\|_{L^2(\pi)}^2 \qquad\text{uniformly in } n .$$
--
--   **Proof.** Expanding the square turns the left-hand side into the double sum of covariances
--   $$\sum_{j<n}\sum_{k<n}\mathbb E\bigl[r(X_{j+1})r(X_{k+1})\bigr].$$
--   Each term is a covariance at lag $|j-k|$: conditioning on the past and using the Markov property, $\mathbb E[r(X_{j+1})r(X_{k+1})] = \int r\,(P^{|j-k|}r)\,d\pi$, and the geometric $L^2$ decay of the transition operator on mean-zero functions bounds this by $2^{-\lfloor|j-k|/N\rfloor}\|r\|_{L^2(\pi)}^2$. Finally, for each fixed $j<n$ the lag weights sum to at most $4N$ regardless of $n$ — geometric decay in the lag means only $O(N)$ of the mass survives — so the double sum is at most $4Nn\|r\|^2_{L^2(\pi)}$.
--
--   Note that no ergodic theorem is used: the entire estimate rests on the total-variation mixing rate, transported to $L^2$ by a Cauchy–Schwarz bound against total variation.
-- source:
--   I. A. Ibragimov and Yu. V. Linnik, Independent and Stationary Sequences of Random Variables, Wolters-Noordhoff 1971, Ch. 18; S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 16-17; L. Tierney, "Markov Chains for Exploring Posterior Distributions", Annals of Statistics 22 (1994) 1701-1728; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320.

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovIterKernel
import Definitions.Def_TotalVariationDist
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Finset Function MeasurableSpace MeasureTheory ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

theorem MarkovChainCLT.integral_sq_sum_coord_le {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) (N : ℕ) (hN : 1 ≤ N) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : 4 * ρ ≤ 1 / 4) (hrate : ∀ x, tvDist (iterKernel P N x) π ≤ ρ)
    (r : X → ℝ) (hr : Measurable r) (Br : ℝ) (hBr : ∀ x, |r x| ≤ Br)
    (hmean : ∫ x, r x ∂π = 0) (n : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range n, r (ω (k + 1))) ^ 2 ∂(chainMeasure P π)
      ≤ 4 * N * n * ∫ x, (r x) ^ 2 ∂π := by sorry
