-- Prove2me | Theorems.Thm_MarkovChainCLT_integrable_sq_scaled_sampleAvg
-- name    : MarkovChainCLT.integrable_sq_scaled_sampleAvg
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-16T01:33:42.87342+00:00
-- url     : https://prove2.me/theorems/62853542-6df5-4447-a607-62d81fe1ee5d
-- title:
--   The CLT-scaled sample average is square integrable
-- statement:
--   **Square integrability of the normalized sample average.** If $r$ is measurable with $\int r^2\,d\pi < \infty$ and $\pi$ is invariant for $P$, then for every $n$ the random variable $\sqrt n\,(\bar r_n - \pi r)$ is square integrable under the stationary path measure.
--
--   **Why this is stated separately.** A bound on a Bochner integral is not by itself a statement about integrability - in Lean an integral of a non-integrable function is defined to be $0$, so an inequality such as $\int (\sqrt n(\bar r_n - \pi r))^2 \le 4N\operatorname{Var}_\pi(r)$ carries no information unless integrability is known independently. Every subsequent step of the truncation argument (Chebyshev-type bounds, the $L^1$-from-$L^2$ comparison, the hypotheses of the approximation lemma) needs the integrability, so it is isolated here.
--
--   **Proof.** Write $c = \pi r$ and $g = r - c$; then $g$ is measurable and square integrable, so $g \in L^2(\pi)$. Because $\pi$ is invariant, the law of each coordinate $\omega \mapsto \omega_{k+1}$ under the stationary path measure is exactly $\pi$; transporting membership in $L^2$ along that pushforward shows each $\omega \mapsto g(\omega_{k+1})$ lies in $L^2$ of the path measure. A finite sum of $L^2$ functions is in $L^2$, hence its square is integrable. Finally, for $n \ge 1$,
--   $$\bigl(\sqrt n(\bar r_n - c)\bigr)^2 = \frac1n\Bigl(\sum_{k=1}^n g(\omega_k)\Bigr)^2,$$
--   a constant multiple of an integrable function; for $n = 0$ the function is identically $0$.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320; P. Billingsley, Probability and Measure, 3rd ed., Wiley 1995, Section 21.

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovErgodicity
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.L2Space

open Filter Finset Function MeasurableSpace MeasureTheory ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

theorem MarkovChainCLT.integrable_sq_scaled_sampleAvg {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π)
    (r : X → ℝ) (hr : Measurable r) (hL2 : Integrable (fun x => (r x) ^ 2) π) (n : ℕ) :
    Integrable (fun ω => (Real.sqrt n * (sampleAvg r n ω - ∫ x, r x ∂π)) ^ 2)
      (chainMeasure P π) := by sorry
