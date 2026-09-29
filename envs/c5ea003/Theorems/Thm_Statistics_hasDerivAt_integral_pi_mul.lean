-- Prove2me | Theorems.Thm_Statistics_hasDerivAt_integral_pi_mul
-- name    : Statistics.hasDerivAt_integral_pi_mul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:32:29.940729+00:00
-- url     : https://prove2.me/theorems/0fbcc078-3249-4268-b416-9c6af43e272b
-- title:
--   Differentiation under the integral for an i.i.d. tilted family: the score of a sample is the sum of scores
-- statement:
--   **Differentiation under the integral sign for an i.i.d. tilted family.** Let $\mu$ be a probability measure on $\Omega$ and let $(L_t)_{t}$ be a family of densities on $\Omega$ with $L_0 \equiv 1$, so that $\mu_t = \mu \cdot L_t$ is a curve of laws through $\mu$. Suppose there is a single measurable envelope $\Psi \in L^2(\mu)$ with $\Psi \ge 1$ such that for all $|t| < \varepsilon$ the map $t \mapsto L_t(x)$ is differentiable with
--   $$|L_t(x)| \le \Psi(x), \qquad |\partial_t L_t(x)| \le \Psi(x).$$
--   Then for every measurable statistic $D \in L^2(\mu^{\otimes T})$ of a sample of size $T$, the map
--   $$t \;\longmapsto\; \mathbb{E}_{\mu_t^{\otimes T}}[D] \;=\; \int D(p) \prod_{i<T} L_t(p_i)\, \mathrm{d}\mu^{\otimes T}(p)$$
--   is differentiable at $t = 0$, with
--   $$\frac{\mathrm{d}}{\mathrm{d}t}\Big|_{t=0} \mathbb{E}_{\mu_t^{\otimes T}}[D] \;=\; \mathbb{E}_{\mu^{\otimes T}}\Bigl[D \cdot \sum_{i<T} \varphi(X_i)\Bigr], \qquad \varphi = \partial_t L_t|_{t=0}.$$
--   That is: **the score of an i.i.d. sample is the sum of the per-observation scores, and the derivative of the expectation of any $L^2$ statistic is its covariance with that score.** This is the regularity half of the Cramér-Rao bound — the half that the inequality itself (`Statistics.information_inequality`) cannot supply — packaged so that a user only has to exhibit one $L^2$ envelope dominating the density and its derivative. The domination argument bounds $\partial_t \prod_i L_t(p_i)$ by $T \prod_i \Psi(p_i)$, which is in $L^2(\mu^{\otimes T})$ because $\Psi \ge 1$, and pairs it with $D$ by Cauchy-Schwarz.
-- source:
--   The classical regularity conditions under which the Cramér-Rao bound applies: E. L. Lehmann and G. Casella, Theory of Point Estimation, 2nd ed., Springer, 1998, Section 2.6, Theorem 6.1 and the conditions (2.6.1)-(2.6.3); A. W. van der Vaart, Asymptotic Statistics, Cambridge University Press, 1998, Section 7.2 (differentiability in quadratic mean and the score of a product experiment).

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

theorem Statistics.hasDerivAt_integral_pi_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {T : ℕ}
    (L L' : ℝ → Ω → ℝ) (D : (Fin T → Ω) → ℝ) {ε : ℝ} (hε : 0 < ε) (Ψ : Ω → ℝ)
    (hL0 : ∀ x, L 0 x = 1)
    (hLmeas : ∀ t, Measurable (L t)) (hL'meas : Measurable (L' 0))
    (hDmeas : Measurable D)
    (hD : MemLp D 2 (Measure.pi fun _ : Fin T => μ))
    (hderiv : ∀ (x : Ω) (t : ℝ), |t| < ε → HasDerivAt (fun t => L t x) (L' t x) t)
    (hΨ1 : ∀ x, 1 ≤ Ψ x)
    (hLbound : ∀ (x : Ω) (t : ℝ), |t| < ε → |L t x| ≤ Ψ x)
    (hL'bound : ∀ (x : Ω) (t : ℝ), |t| < ε → |L' t x| ≤ Ψ x)
    (hΨmeas : Measurable Ψ) (hΨL2 : MemLp Ψ 2 μ) :
    HasDerivAt (fun t => ∫ p, D p * ∏ i, L t (p i) ∂(Measure.pi fun _ : Fin T => μ))
      (∫ p, D p * ∑ i : Fin T, L' 0 (p i) ∂(Measure.pi fun _ : Fin T => μ)) 0 := by sorry
