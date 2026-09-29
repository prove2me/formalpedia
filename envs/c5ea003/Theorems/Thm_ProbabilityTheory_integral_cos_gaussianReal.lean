-- Prove2me | Theorems.Thm_ProbabilityTheory_integral_cos_gaussianReal
-- name    : ProbabilityTheory.integral_cos_gaussianReal
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-16T01:07:04.387361+00:00
-- url     : https://prove2.me/theorems/d57706b1-6eb8-47fb-bf49-63021fa542ce
-- title:
--   The cosine integral against a centred Gaussian
-- statement:
--   **The cosine integral against a centred Gaussian.** For every $v \ge 0$,
--   $$\int_{\mathbb R} \cos x \; dN(0,v)(x) \;=\; e^{-v/2}.$$
--
--   **Why this identity is useful.** $\cos$ is a bounded $1$-Lipschitz function, so it is admissible both as a test function for weak convergence and for the elementary bound $|\cos a - \cos b| \le |a-b|$. The identity above says that integrating this one test function against $N(0,v)$ recovers $v$ injectively. That turns an estimate on laws into an estimate on variances: if two centred Gaussians are close when tested against $\cos$, their variances are close, provided they range in a bounded set. This is precisely the mechanism used to show that the truncated asymptotic variances in the Markov chain central limit theorem form a Cauchy sequence.
--
--   **Proof.** This is the real part of the characteristic function at $t = 1$. The characteristic function of $N(\mu, v)$ is $t \mapsto \exp(it\mu - vt^2/2)$; at $\mu = 0$, $t = 1$ it equals $e^{-v/2}$, a real number. On the other hand $\varphi(1) = \int e^{ix}\,dN(0,v)(x)$, and the integrand is bounded in modulus by $1$, hence integrable against a probability measure; taking real parts commutes with the Bochner integral for integrable functions, and $\operatorname{Re} e^{ix} = \cos x$. Comparing gives the claim.
-- source:
--   W. Feller, An Introduction to Probability Theory and Its Applications, Vol. II, 2nd ed., Wiley 1971, Chapter XV (characteristic functions); P. Billingsley, Probability and Measure, 3rd ed., Wiley 1995, Section 26.

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

theorem ProbabilityTheory.integral_cos_gaussianReal (v : ℝ≥0) :
    ∫ x, Real.cos x ∂(gaussianReal 0 v) = Real.exp (-(v : ℝ) / 2) := by sorry
