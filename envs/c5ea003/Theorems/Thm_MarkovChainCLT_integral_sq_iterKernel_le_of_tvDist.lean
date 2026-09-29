-- Prove2me | Theorems.Thm_MarkovChainCLT_integral_sq_iterKernel_le_of_tvDist
-- name    : MarkovChainCLT.integral_sq_iterKernel_le_of_tvDist
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-16T00:02:21.109541+00:00
-- url     : https://prove2.me/theorems/00f40de6-4819-4bea-8c0c-d05da4c855c6
-- title:
--   Uniform mixing makes the transition operator an $L^2$ contraction on mean-zero functions
-- statement:
--   **A uniformly ergodic chain contracts $L^2_0(\pi)$.** If the $N$-step kernel satisfies the uniform total-variation bound $\sup_x\|P^N(x,\cdot)-\pi\| \le \rho$, then for every square-integrable $h$ with $\mathbb E_\pi h = 0$,
--   $$\bigl\|P^N h\bigr\|_{L^2(\pi)}^2 \;\le\; 4\rho\,\|h\|_{L^2(\pi)}^2, \qquad\text{i.e.}\qquad \bigl\|P^Nh\bigr\|_{L^2(\pi)} \le 2\sqrt{\rho}\,\|h\|_{L^2(\pi)} .$$
--
--   **Why this is the bridge from bounded to square-integrable observables.** For a *bounded* $h$, uniform ergodicity gives $\|P^nh - \pi h\|_\infty \le 2\|h\|_\infty Rt^n$ directly, and everything — the Poisson equation, the martingale approximation, the central limit theorem — follows easily. For a merely square-integrable $h$ that estimate is unavailable, and the sup-norm must be replaced by the $L^2$ norm. Interpolating naively fails; what works is the Cauchy–Schwarz bound against total variation, which costs a *square root* of the mixing rate but keeps the $L^2$ norm on the right-hand side.
--
--   Since $\rho$ can be made as small as one likes by taking $N$ large (uniform ergodicity gives $\rho \le Rt^N$), choosing $\rho < 1/4$ makes $P^N$ a **strict contraction** of the mean-zero subspace $L^2_0(\pi)$, so that $\|P^n h\|_{L^2(\pi)}$ decays geometrically. This is what makes the Neumann series $\hat h = \sum_{n\ge0}P^n h$ converge in $L^2$ — solving the Poisson equation for square-integrable data — and what yields the summable covariances $|\operatorname{Cov}(h(X_0),h(X_n))| \le \|h\|_2\|P^nh\|_2$ behind the $O(n)$ variance bound for partial sums.
--
--   **Proof.** For $\pi$-almost every $x$ the measure $P^N(x,\cdot)$ integrates $h^2$ (because $\int\!\!\int h^2\,dP^N(x,\cdot)\,d\pi(x) = \int h^2 d\pi < \infty$ by invariance), so the square-root total-variation inequality applies with $\mu = P^N(x,\cdot)$, $\nu = \pi$. Using $\int h\,d\pi = 0$,
--   $$\bigl|(P^Nh)(x)\bigr| \;\le\; \sqrt{\rho}\,\Bigl(\sqrt{\textstyle\int h^2\,dP^N(x,\cdot)} + \|h\|_{L^2(\pi)}\Bigr).$$
--   Squaring and using $(a+b)^2 \le 2(a^2+b^2)$,
--   $$(P^Nh)(x)^2 \;\le\; 2\rho\Bigl(\int h^2\,dP^N(x,\cdot) + \|h\|_{L^2(\pi)}^2\Bigr),$$
--   and integrating in $x$ against $\pi$ — where invariance turns $\int\!\!\int h^2\,dP^N(x,\cdot)\,d\pi(x)$ back into $\|h\|_{L^2(\pi)}^2$ — gives the factor $4\rho$.
-- source:
--   S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 16 (Theorem 16.0.2); E. Nummelin, General Irreducible Markov Chains and Non-negative Operators, Cambridge 1984, Ch. 6; L. Tierney, "Markov Chains for Exploring Posterior Distributions", Annals of Statistics 22 (1994) 1701-1728; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, Section 2.

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovIterKernel
import Definitions.Def_TotalVariationDist
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Function MeasurableSpace MeasureTheory ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

theorem MarkovChainCLT.integral_sq_iterKernel_le_of_tvDist {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) (N : ℕ) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ∀ x, tvDist (iterKernel P N x) π ≤ ρ)
    (h : X → ℝ) (hh : Measurable h) (hL2 : Integrable (fun x => (h x) ^ 2) π)
    (hmean : ∫ x, h x ∂π = 0) :
    ∫ x, (∫ y, h y ∂(iterKernel P N x)) ^ 2 ∂π ≤ 4 * ρ * ∫ x, (h x) ^ 2 ∂π := by sorry
