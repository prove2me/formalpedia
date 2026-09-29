-- Prove2me | Theorems.Thm_MarkovChainCLT_poissonEquation_of_bounded_of_uniformlyErgodic
-- name    : MarkovChainCLT.poissonEquation_of_bounded_of_uniformlyErgodic
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T23:00:39.633462+00:00
-- url     : https://prove2.me/theorems/3141610f-2e21-423e-a238-1231b0389e51
-- title:
--   Bounded solution of the Poisson equation for a uniformly ergodic chain
-- statement:
--   **The Poisson equation for a bounded observable of a uniformly ergodic chain.** If $P$ is uniformly ergodic with invariant law $\pi$ and $\varphi$ is bounded and measurable, then there is a **bounded** measurable $g$ with
--   $$g(x) - (Pg)(x) \;=\; \varphi(x) - \mathbb E_\pi\varphi \qquad\text{for every } x .$$
--
--   **Why one wants it.** The Poisson equation is the engine of the martingale approximation for Markov chains. Once $g$ solves it, the partial sums of the centred observable telescope into a martingale plus a bounded remainder,
--   $$\sum_{k<n}\bigl(\varphi(X_{k+1}) - \mathbb E_\pi\varphi\bigr) \;=\; \sum_{k<n}\underbrace{\bigl(g(X_{k+1}) - (Pg)(X_k)\bigr)}_{\text{martingale differences}} \;+\; (Pg)(X_0) - (Pg)(X_n),$$
--   and every limit theorem for the chain becomes a limit theorem for a martingale. Boundedness of $g$ is what makes the differences bounded, the remainder $O(1)$, and the whole argument elementary; solving the same equation in $L^2$ for a merely square-integrable $\varphi$ is a genuinely harder problem.
--
--   **Construction.** Set $u_n(x) = \int\varphi\,dP^n(x,\cdot) - \mathbb E_\pi\varphi$ and
--   $$g \;=\; \sum_{n\ge 0} u_n .$$
--   Uniform ergodicity gives $\sup_x\|P^n(x,\cdot)-\pi\| \le Rt^n$ with $t<1$, and testing against a function bounded by $B$ costs at most twice the total variation, so
--   $$|u_n(x)| \;\le\; 2B\,R\,t^n \quad (n\ge1), \qquad |u_0(x)| \le 2B .$$
--   The series therefore converges **uniformly and absolutely**, with a majorant that is geometric in $n$ and independent of $x$; $g$ is bounded, and measurable as a pointwise limit of its partial sums.
--
--   **Verification.** Applying one step of the chain shifts the index. Because $P^n \circ P = P^{n+1}$ (an easy induction from associativity of kernel composition), Fubini for the composed kernel gives $\int u_n\,dP(x,\cdot) = u_{n+1}(x)$, and the geometric majorant justifies exchanging the integral with the sum. Hence
--   $$(Pg)(x) \;=\; \sum_{n\ge0}u_{n+1}(x) \;=\; g(x) - u_0(x) \;=\; g(x) - \bigl(\varphi(x) - \mathbb E_\pi\varphi\bigr),$$
--   which is the assertion. Note the identity holds at **every** $x$, not merely $\pi$-almost everywhere, because the convergence is uniform.
-- source:
--   M. I. Gordin and B. A. Lifsic, "The central limit theorem for stationary Markov processes", Soviet Math. Dokl. 19 (1978) 392-394; E. Nummelin, General Irreducible Markov Chains and Non-negative Operators, Cambridge 1984, Ch. 5; S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 17; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, Section 2.

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovIterKernel
import Definitions.Def_TotalVariationDist
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory ProbabilityTheory Filter
open MarkovChainCLT
open scoped ENNReal NNReal Topology

theorem MarkovChainCLT.poissonEquation_of_bounded_of_uniformlyErgodic {X : Type*}
    [MeasurableSpace X] (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (huni : UniformlyErgodic P π) (φ : X → ℝ) (hφ : Measurable φ)
    (B : ℝ) (hB : ∀ x, |φ x| ≤ B) :
    ∃ g : X → ℝ, Measurable g ∧ (∃ C : ℝ, ∀ x, |g x| ≤ C) ∧
      ∀ x, g x - ∫ y, g y ∂(P x) = φ x - ∫ y, φ y ∂π := by sorry
