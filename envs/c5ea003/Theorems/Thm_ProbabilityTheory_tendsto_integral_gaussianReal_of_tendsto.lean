-- Prove2me | Theorems.Thm_ProbabilityTheory_tendsto_integral_gaussianReal_of_tendsto
-- name    : ProbabilityTheory.tendsto_integral_gaussianReal_of_tendsto
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-16T01:12:20.187002+00:00
-- url     : https://prove2.me/theorems/04bd6983-40b3-41ef-96a9-46ea89fda32b
-- title:
--   Centred Gaussians depend weakly continuously on their variance
-- statement:
--   **The centred Gaussian law depends continuously on its variance, in the weak topology.** If $v_K \to v$ in $[0,\infty)$ then $N(0, v_K) \Rightarrow N(0, v)$. Concretely: for every bounded Lipschitz $f : \mathbb R \to \mathbb R$,
--   $$\int f \, dN(0, v_K) \;\longrightarrow\; \int f \, dN(0, v).$$
--
--   Bounded Lipschitz test functions suffice to determine weak convergence (the bounded-Lipschitz metric metrizes it on a separable metric space), so the displayed statement is equivalent to $N(0,v_K) \Rightarrow N(0,v)$; it is stated in integral form because that is the form in which it is consumed. Note that no continuity at $v = 0$ needs to be excluded: $N(0,0)$ is the Dirac mass at $0$ and the statement remains true there.
--
--   **Where this is used.** In the central limit theorem for a square-integrable observable of a uniformly ergodic Markov chain, the observable is truncated at level $K$; the bounded case gives $S_n(f_K)/\sqrt n \Rightarrow N(0, v_K)$, and the truncated variances are shown to be Cauchy, say $v_K \to v$. The final $3\varepsilon$ argument then needs to replace $N(0,v_K)$ by $N(0,v)$ at a cost that vanishes with $K$, which is exactly this lemma.
--
--   **Proof.** Every centred Gaussian is a rescaled standard Gaussian: $N(0,t)$ is the pushforward of $N(0,1)$ under $y \mapsto \sqrt t\, y$. Changing variables,
--   $$\int f \, dN(0,t) = \int f(\sqrt t\, y)\, dN(0,1)(y),$$
--   the integrand being continuous and bounded, hence integrable. For two variances $t$ and $v$ the Lipschitz property gives the pointwise bound $|f(\sqrt t y) - f(\sqrt v y)| \le L\,|\sqrt t - \sqrt v|\,|y|$, so
--   $$\Bigl|\int f \, dN(0,t) - \int f \, dN(0,v)\Bigr| \;\le\; L\,|\sqrt t - \sqrt v| \int |y| \, dN(0,1)(y),$$
--   and the standard Gaussian has a finite first absolute moment. Since $\sqrt\cdot$ is continuous, the right-hand side tends to $0$ as $t \to v$, and a squeeze finishes the proof.
-- source:
--   P. Billingsley, Convergence of Probability Measures, 2nd ed., Wiley 1999, Section 1 and Theorem 2.1; W. Feller, An Introduction to Probability Theory and Its Applications, Vol. II, 2nd ed., Wiley 1971, Chapter VIII.

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Portmanteau

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

theorem ProbabilityTheory.tendsto_integral_gaussianReal_of_tendsto (u : ℕ → ℝ≥0) (c : ℝ≥0)
    (hu : Tendsto (fun K => (u K : ℝ)) atTop (𝓝 (c : ℝ)))
    (f : ℝ → ℝ) (L : ℝ≥0) (hL : LipschitzWith L f) (C : ℝ)
    (hC : ∀ x y, dist (f x) (f y) ≤ C) :
    Tendsto (fun K => ∫ x, f x ∂(gaussianReal 0 (u K))) atTop
      (𝓝 (∫ x, f x ∂(gaussianReal 0 c))) := by sorry
