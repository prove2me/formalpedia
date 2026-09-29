-- Prove2me | Theorems.Thm_MarkovChainCLT_integral_mul_coord_eq
-- name    : MarkovChainCLT.integral_mul_coord_eq
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-16T00:26:01.13525+00:00
-- url     : https://prove2.me/theorems/52b23b87-a021-46cb-8b37-52b173d9fb64
-- title:
--   Chain covariance at lag $d$ equals the inner product against $P^d$
-- statement:
--   **Chain covariances are inner products against the transition operator.** For a stationary chain and a bounded measurable $r$,
--   $$\mathbb E\bigl[r(X_j)\,r(X_{j+d})\bigr] \;=\; \int r\,(P^d r)\,d\pi \qquad\text{for all } j,d,$$
--   where $(P^dr)(x) = \int r\,dP^d(x,\cdot)$. In particular the covariance depends on $j$ and $j+d$ only through the lag $d$ — stationarity — and it is computed by a single integral over the state space rather than over path space.
--
--   **Why this identity is the crux of the $L^2$ theory.** Combined with Cauchy–Schwarz it gives
--   $$\bigl|\mathbb E[r(X_j)r(X_{j+d})]\bigr| \;\le\; \|r\|_{L^2(\pi)}\,\|P^dr\|_{L^2(\pi)},$$
--   so any geometric decay of $\|P^dr\|_{L^2(\pi)}$ — which uniform ergodicity supplies — makes the covariances absolutely summable. Expanding the square of a partial sum then yields
--   $$\operatorname{Var}\Bigl(\sum_{k<n}r(X_k)\Bigr) \;=\; \sum_{j,k<n}\mathbb E[r(X_j)r(X_k)] \;\le\; C\,n\,\|r\|_{L^2(\pi)}^2$$
--   with $C$ depending only on the chain, **not** on $\|r\|_\infty$. That is precisely the estimate needed to control the truncation error when the Markov chain central limit theorem is extended from bounded to merely square-integrable observables: the martingale approximation is available only for bounded data, and this bound says the discarded remainder contributes $O(\|r\|_{L^2}^2)$ to the normalized variance, uniformly in $n$.
--
--   **Proof.** Condition on the past up to time $j$. The Markov property at lag $d$ gives $\mathbb E[r(X_{j+d})\mid\sigma(X_0,\dots,X_j)] = (P^dr)(X_j)$, and $r(X_j)$ is measurable with respect to that $\sigma$-algebra, so the pull-out property of conditional expectation yields
--   $$\mathbb E\bigl[r(X_j)r(X_{j+d})\mid\sigma(X_{\le j})\bigr] \;=\; r(X_j)\,(P^dr)(X_j).$$
--   Taking expectations — conditional expectation preserves the integral — and using that each coordinate of the stationary chain has law $\pi$ turns the path-space integral into the state-space integral $\int r\,(P^dr)\,d\pi$.
-- source:
--   J. Neveu, Mathematical Foundations of the Calculus of Probability, Holden-Day 1965, Ch. V; I. A. Ibragimov and Yu. V. Linnik, Independent and Stationary Sequences of Random Variables, Wolters-Noordhoff 1971; S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 17; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320.

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovIterKernel
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder
  ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

theorem MarkovChainCLT.integral_mul_coord_eq {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π)
    (r : X → ℝ) (hr : Measurable r) (Br : ℝ) (hBr : ∀ x, |r x| ≤ Br) (j d : ℕ) :
    ∫ ω, r (ω (j + 1)) * r (ω (j + 1 + d)) ∂(chainMeasure P π)
      = ∫ x, r x * (∫ y, r y ∂(iterKernel P d x)) ∂π := by sorry
