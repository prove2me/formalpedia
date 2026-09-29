-- Prove2me | Theorems.Thm_MarkovChainCLT_poissonEquation_ae_of_uniformlyErgodic
-- name    : MarkovChainCLT.poissonEquation_ae_of_uniformlyErgodic
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T18:28:38.540605+00:00
-- url     : https://prove2.me/theorems/21b0a56b-54f2-48b7-90cc-2a61ddfa84fc
-- title:
--   Uniform ergodicity solves the Poisson equation $\pi$-a.e. in $L^2$
-- statement:
--   Let $X$ be a uniformly ergodic Markov chain with invariant distribution $\pi$, so that $\|P^n(x,\cdot) - \pi\| \le R\,t^n$ with $R$ **independent of the starting point** and $t < 1$, and let $f \in L^2(\pi)$. Then the **Poisson equation**
--
--   $$\hat g - P\hat g \;=\; f - E_\pi f$$
--
--   has a solution $\hat g \in L^2(\pi)$, with $P\hat g \in L^2(\pi)$, the equation holding for $\pi$-almost every $x$.
--
--   The solution is the geometric series $\hat g = \sum_{n \ge 0} P^n \bar f$ with $\bar f = f - E_\pi f$. Uniform ergodicity is exactly what makes it converge: the Dobrushin contraction coefficient of $P^n$ is bounded by $\sup_x \|P^n(x,\cdot) - \pi\| \le R t^n$, and the Dobrushin coefficient dominates the operator norm of $P^n$ on $L^p_0(\pi)$ for every $p$ by interpolation between $L^1$ and $L^\infty$. So $\|P^n\bar f\|_2$ decays geometrically, the series converges in $L^2$, and telescoping it gives the equation. That $P\hat g \in L^2$ is then automatic, a Markov kernel being an $L^2(\pi)$-contraction by Jensen and invariance.
--
--   **Why the conclusion is almost-everywhere and not pointwise.** An $L^2$ limit is only determined up to a $\pi$-null set, so no pointwise representative is canonical. More seriously, the left-hand side need not be *meaningful* at every point: $f \in L^2(\pi)$ does not give $f \in L^1(P(x,\cdot))$ for every $x$, because $P(x,\cdot)$ need not be absolutely continuous with respect to $\pi$; at such an $x$ the integral $\int \hat g \,\mathrm{d}P(x,\cdot)$ is not defined (and is $0$ by the usual Bochner convention), so a pointwise equation would force $\hat g(x) = f(x) - E_\pi f$ there for no reason. Repairing $\hat g$ on the exceptional set does not help, since it breaks the equation at every $x$ whose $P(x,\cdot)$ charges that set.
--
--   The weakening costs nothing downstream. In the martingale-approximation proof of the central limit theorem the equation is only ever evaluated along the trajectory, and every coordinate of the stationary chain has law $\pi$, so a $\pi$-a.e. identity holds almost surely at every coordinate simultaneously (a countable intersection of full-measure events).
--
--   This supersedes an earlier version of this statement that quantified over every $x$; that form is believed unprovable for the reason above.
-- source:
--   L. Tierney, "Markov Chains for Exploring Posterior Distributions", Annals of Statistics 22 (1994) 1701-1728, Theorem 5; the martingale-approximation proof is M. I. Gordin (1969) and C. Kipnis, S. R. S. Varadhan, Comm. Math. Phys. 104 (1986) 1-19, Corollary 1.5. Cited as the route to Corollary 5 in G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Remark 8.

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem MarkovChainCLT.poissonEquation_ae_of_uniformlyErgodic {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (huni : UniformlyErgodic P π)
    (f : X → ℝ) (hf : Measurable f) (hL2 : MemLp f 2 π) :
    ∃ g : X → ℝ, Measurable g ∧ MemLp g 2 π ∧
      Measurable (fun x => ∫ y, g y ∂(P x)) ∧
      MemLp (fun x => ∫ y, g y ∂(P x)) 2 π ∧
      ∀ᵐ x ∂π, g x - ∫ y, g y ∂(P x) = f x - ∫ x, f x ∂π := by sorry
