-- Prove2me | Theorems.Thm_ProbabilityTheory_integral_abs_le_sqrt_integral_sq
-- name    : ProbabilityTheory.integral_abs_le_sqrt_integral_sq
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-16T01:22:12.347193+00:00
-- url     : https://prove2.me/theorems/e029d57d-93a0-430f-bafa-dd0d4a1f1c87
-- title:
--   The L¹ norm is dominated by the L² norm on a probability space
-- statement:
--   **Cauchy-Schwarz against the constant $1$.** On a probability space,
--   $$\mathbb E|Z| \;\le\; \sqrt{\mathbb E[Z^2]} .$$
--
--   **Where this is used.** In the truncation argument for the Markov chain central limit theorem, the available control on $Y_n - W^K_n$ is a *second-moment* bound coming from the $O(n)$ variance estimate for partial sums, whereas the approximation lemma that closes the argument consumes a *first-moment* bound. This inequality is the bridge, and it is the reason the final approximation error is $2\sqrt{N}\,\|f - f_K\|_{L^2(\pi)}$ rather than something involving an $L^1$ modulus.
--
--   **Proof.** Rather than invoking the Cauchy-Schwarz inequality, use the elementary weighted arithmetic-geometric bound: for every $\varepsilon > 0$ and every real $z$,
--   $$|z| \;\le\; \frac{\varepsilon}{2} + \frac{z^2}{2\varepsilon},$$
--   which is just $(\varepsilon - |z|)^2 \ge 0$ divided by $2\varepsilon$. Integrating gives $\mathbb E|Z| \le \varepsilon/2 + \mathbb E[Z^2]/(2\varepsilon)$ for every $\varepsilon > 0$. If $S := \mathbb E[Z^2] > 0$, choosing $\varepsilon = \sqrt S$ makes the right-hand side exactly $\sqrt S$. If $S = 0$ then $Z^2 = 0$ almost everywhere, hence $|Z| = 0$ almost everywhere and both sides vanish. (Integrability of $|Z|$ itself follows from that of $Z^2$ on a probability space.)
-- source:
--   P. Billingsley, Probability and Measure, 3rd ed., Wiley 1995, Section 21 (Lyapunov's inequality); W. Rudin, Real and Complex Analysis, 3rd ed., McGraw-Hill 1987, Chapter 3.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

theorem ProbabilityTheory.integral_abs_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hZ : Measurable Z)
    (hsq : Integrable (fun ω => (Z ω) ^ 2) μ) :
    ∫ ω, |Z ω| ∂μ ≤ Real.sqrt (∫ ω, (Z ω) ^ 2 ∂μ) := by sorry
