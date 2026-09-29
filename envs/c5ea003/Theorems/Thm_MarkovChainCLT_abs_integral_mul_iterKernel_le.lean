-- Prove2me | Theorems.Thm_MarkovChainCLT_abs_integral_mul_iterKernel_le
-- name    : MarkovChainCLT.abs_integral_mul_iterKernel_le
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-16T00:33:05.422419+00:00
-- url     : https://prove2.me/theorems/f32bdf20-6fe9-484c-bea3-24c0bb541a27
-- title:
--   Geometric decay of the autocovariance, with an $L^2$ constant
-- statement:
--   **The autocovariance of a uniformly ergodic chain decays geometrically.** For a bounded measurable $r$ with $\mathbb E_\pi r = 0$,
--   $$\Bigl|\int r\,(P^dr)\,d\pi\Bigr| \;\le\; 2^{-\lfloor d/N\rfloor}\,\|r\|_{L^2(\pi)}^2 ,$$
--   whenever the $N$-step kernel satisfies $\sup_x\|P^N(x,\cdot)-\pi\|\le\rho$ with $4\rho\le1/4$. Since $\int r\,(P^dr)\,d\pi = \mathbb E[r(X_0)r(X_d)]$ for the stationary chain, this is exactly the statement that the autocovariance function decays geometrically in the lag, **with a constant proportional to $\|r\|_{L^2(\pi)}^2$ rather than to $\|r\|_\infty^2$.**
--
--   **Why the $L^2$ constant matters.** The martingale approximation behind the Markov chain central limit theorem is available only for bounded observables. To reach a square-integrable $f$ one truncates, $f = f_K + r_K$, and must show the discarded part contributes negligibly to the normalized variance. That requires a bound on $\operatorname{Var}\bigl(\sum_{k<n}r_K(X_k)\bigr)$ in terms of $\|r_K\|_{L^2(\pi)}$ — a sup-norm bound is useless, since $\|r_K\|_\infty$ does not go to zero. Summing the estimate above over lags gives
--   $$\sum_{d\ge0}\Bigl|\int r\,(P^dr)\,d\pi\Bigr| \;\le\; 2N\,\|r\|_{L^2(\pi)}^2 ,$$
--   because each block of $N$ consecutive lags contributes at most $N2^{-q}\|r\|_2^2$; expanding the square of a partial sum then yields $\operatorname{Var}(\sum_{k<n}r(X_k)) = O(n\|r\|_{L^2(\pi)}^2)$.
--
--   **Proof.** Cauchy–Schwarz would give $\|r\|_2\|P^dr\|_2$, and $\|P^dr\|_2 \le 2^{-\lfloor d/N\rfloor}\|r\|_2$ by the geometric decay of the transition operator. The proof here uses the equivalent weighted arithmetic–geometric mean inequality, which avoids square roots entirely: with $\alpha = 2^{-\lfloor d/N\rfloor}$,
--   $$|r\,(P^dr)| \;\le\; \tfrac12\bigl(\alpha\,r^2 + \alpha^{-1}(P^dr)^2\bigr) \qquad\text{pointwise},$$
--   since $(\alpha|r| - |P^dr|)^2 \ge 0$. Integrating and inserting $\|P^dr\|_2^2 \le \alpha^2\|r\|_2^2$ makes the two terms equal, each $\tfrac12\alpha\|r\|_2^2$, and the bound closes.
-- source:
--   I. A. Ibragimov and Yu. V. Linnik, Independent and Stationary Sequences of Random Variables, Wolters-Noordhoff 1971; S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 16-17; L. Tierney, "Markov Chains for Exploring Posterior Distributions", Annals of Statistics 22 (1994) 1701-1728; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320.

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovIterKernel
import Definitions.Def_TotalVariationDist
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Finset Function MeasurableSpace MeasureTheory ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

theorem MarkovChainCLT.abs_integral_mul_iterKernel_le {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) (N : ℕ) (hN : 1 ≤ N) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : 4 * ρ ≤ 1 / 4) (hrate : ∀ x, tvDist (iterKernel P N x) π ≤ ρ)
    (r : X → ℝ) (hr : Measurable r) (Br : ℝ) (hBr : ∀ x, |r x| ≤ Br)
    (hmean : ∫ x, r x ∂π = 0) (d : ℕ) :
    |∫ x, r x * (∫ y, r y ∂(iterKernel P d x)) ∂π|
      ≤ (1 / 2 : ℝ) ^ (d / N) * ∫ x, (r x) ^ 2 ∂π := by sorry
