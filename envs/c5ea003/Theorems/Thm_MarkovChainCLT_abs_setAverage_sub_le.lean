-- Prove2me | Theorems.Thm_MarkovChainCLT_abs_setAverage_sub_le
-- name    : MarkovChainCLT.abs_setAverage_sub_le
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T21:14:13.509887+00:00
-- url     : https://prove2.me/theorems/4c727a00-78e6-4a0d-94ad-df40a2956af6
-- title:
--   An average over a set inherits a pointwise bound on that set
-- statement:
--   Let $\rho$ be a finite measure, $s$ a measurable set with $\rho(s) \ne 0$, and $h$ an integrable function on $s$. If $|h(u) - m| \le C$ for every $u \in s$, then the average of $h$ over $s$ satisfies the same bound:
--
--   $$\left| \frac{1}{\rho(s)}\int_s h \,\mathrm{d}\rho \;-\; m \right| \;\le\; C.$$
--
--   **What it is for.** This is the final, purely real-analytic step of a mixing-coefficient estimate, and it is what makes such an estimate *uniform in the split point*. After the probabilistic work — disintegrating a "past $\cap$ future" probability over the past, and identifying the conditional probability of the future as a chain restarted from $P^n(u_k,\cdot)$ — one arrives at exactly this shape:
--   $$\frac{\mathbb{P}(A \cap B)}{\mathbb{P}(A)} - \mathbb{P}(B) \;=\; \frac{1}{\rho(A_0)}\int_{A_0}\Bigl[\underbrace{\textstyle\int g\,\mathrm{d}P^n(u_k,\cdot)}_{h(u)} - \underbrace{\textstyle\int g \,\mathrm{d}\pi}_{m}\Bigr]\mathrm{d}\rho(u),$$
--   with a pointwise bound $|h(u)-m| \le \|P^n(u_k,\cdot)-\pi\| \le C$ available for every $u$. The conclusion $\phi(n) \le C$ then follows for *every* choice of past event $A$ and split point $k$, which is precisely what the supremum in the definition of the mixing coefficient requires.
--
--   Stated separately because it is where the argument stops being about Markov chains: no measure-theoretic structure beyond finiteness, no kernel, no filtration — only the elementary fact that averaging cannot leave the range of the values being averaged.
--
--   **Proof.** Since $\rho(s) \ne 0$ and $\rho$ is finite, $\rho(s)$ is a strictly positive real. Centring, $\int_s h \,\mathrm{d}\rho - \rho(s)\,m = \int_s (h - m)\,\mathrm{d}\rho$. Then
--   $$\Bigl|\int_s (h-m)\,\mathrm{d}\rho\Bigr| \;\le\; \int_s |h-m|\,\mathrm{d}\rho \;\le\; \int_s C \,\mathrm{d}\rho \;=\; C\,\rho(s),$$
--   the first step by the triangle inequality for integrals, the second by monotonicity (the hypothesis holds pointwise on $s$, hence almost everywhere for the restricted measure). Dividing by $\rho(s) > 0$ gives the claim.
-- source:
--   R. C. Bradley, "Basic Properties of Strong Mixing Conditions. A Survey and Some Open Questions", Probability Surveys 2 (2005) 107-144; P. Billingsley, Convergence of Probability Measures, 2nd ed., Wiley 1999, Section 20; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, Section 3.

import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory
open scoped ENNReal NNReal

theorem MarkovChainCLT.abs_setAverage_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (s : Set Ω) (hs : MeasurableSet s) (hρs : ρ s ≠ 0)
    (h : Ω → ℝ) (hint : IntegrableOn h s ρ) (m C : ℝ)
    (hbd : ∀ u ∈ s, |h u - m| ≤ C) :
    |(∫ u in s, h u ∂ρ) / (ρ s).toReal - m| ≤ C := by sorry
