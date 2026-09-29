-- Prove2me | Theorems.Thm_MarkovChainCLT_condExp_coord_add
-- name    : MarkovChainCLT.condExp_coord_add
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-16T00:08:25.838384+00:00
-- url     : https://prove2.me/theorems/1aa23f9e-c9bc-4b64-ac1b-a13fba1a4682
-- title:
--   The Markov property at an arbitrary lag
-- statement:
--   **The Markov property at an arbitrary lag.** For a bounded measurable $h$ and any $m, d$,
--   $$\mathbb E\bigl[h(X_{m+d}) \,\big|\, \sigma(X_0,\dots,X_m)\bigr] \;=\; (P^d h)(X_m) \qquad\text{almost surely},$$
--   where $(P^dh)(x) = \int h\,dP^d(x,\cdot)$. This holds for every initial distribution.
--
--   **Why the lagged form is needed.** The one-step version is what makes the Poisson-equation differences a martingale. The lagged version is what computes **covariances along the chain**: for bounded $u,v$ and $j\le k$,
--   $$\mathbb E\bigl[u(X_j)\,v(X_k)\bigr] \;=\; \mathbb E\bigl[u(X_j)\,\mathbb E[v(X_k)\mid\sigma(X_0,\dots,X_j)]\bigr] \;=\; \mathbb E\bigl[u(X_j)\,(P^{k-j}v)(X_j)\bigr] \;=\; \int u\,(P^{k-j}v)\,d\pi$$
--   under the stationary chain. Combined with the $L^2$ contraction $\|P^n v\|_{L^2(\pi)} \le C\kappa^n\|v\|_{L^2(\pi)}$ of a uniformly ergodic chain, this gives absolutely summable covariances and hence the variance bound
--   $$\operatorname{Var}\Bigl(\sum_{k<n} v(X_k)\Bigr) \;\le\; C'\,n\,\|v\|_{L^2(\pi)}^2$$
--   with a constant depending only on $P$ — the estimate that controls the truncation error when passing from bounded to square-integrable observables in the Markov chain central limit theorem.
--
--   **Proof.** Induction on $d$. For $d=0$ the kernel is the Dirac kernel, so the left side is $h(X_m)$, which is already measurable with respect to the conditioning $\sigma$-algebra. For the inductive step, condition first on the larger $\sigma$-algebra $\sigma(X_0,\dots,X_{m+d})$: by the tower property,
--   $$\mathbb E\bigl[h(X_{m+d+1})\mid\sigma(X_{\le m})\bigr] = \mathbb E\Bigl[\mathbb E\bigl[h(X_{m+d+1})\mid\sigma(X_{\le m+d})\bigr]\;\Big|\;\sigma(X_{\le m})\Bigr] = \mathbb E\bigl[(Ph)(X_{m+d})\mid\sigma(X_{\le m})\bigr],$$
--   using the one-step Markov property. Since $Ph$ is again bounded and measurable, the induction hypothesis applies to it and yields $(P^d(Ph))(X_m)$, which is $(P^{d+1}h)(X_m)$ because $P^{d+1} = P\circ P^d$ — Fubini for a composed kernel.
-- source:
--   J. Neveu, Mathematical Foundations of the Calculus of Probability, Holden-Day 1965, Ch. V; S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 3; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, Section 2.

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovIterKernel
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder
  ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

theorem MarkovChainCLT.condExp_coord_add {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (lam : Measure X) [IsProbabilityMeasure lam]
    (h : X → ℝ) (hh : Measurable h) (B : ℝ) (hB : ∀ x, |h x| ≤ B) (m d : ℕ) :
    (fun ω : ℕ → X => ∫ y, h y ∂(iterKernel P d (ω m)))
      =ᵐ[chainMeasure P lam] (chainMeasure P lam)[fun ω : ℕ → X => h (ω (m + d)) |
        MeasurableSpace.comap (frestrictLe (π := fun _ : ℕ => X) m) inferInstance] := by sorry
