-- Prove2me | Theorems.Thm_talagrand_tangent_sampling_bennett_log_tail_from_bernstein_bridge_dense
-- name    : talagrand_tangent_sampling_bennett_log_tail_from_bernstein_bridge_dense
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-25T02:35:27.684499+00:00
-- url     : https://prove2.me/theorems/b55651b1-4a8f-412d-912f-7d4487ba90eb
-- title:
--   Bennett–Bernstein tail-shape bridge: $h(u)\ge\frac{u^2}{2+2u/3}$
-- statement:
--   **R2 — Bennett–log ↔ Bernstein tail-shape bridge (dimensionless form).** Bennett's function dominates the Bernstein quadratic: $h(u)=(1+u)\log(1+u)-u\ge u^2/(2+2u/3)$ for all $u\ge 0$. The σ²-aware entropy-method spine produces the Bernstein-form tail exponent, whereas the density-absorption node `talagrand_tangent_exponential_tail_absorbs_into_polynomial_failure_dense` consumes the tighter Bennett-log exponent; substituting $u=B x/v$ and rescaling by $v/B^2$ turns this scalar fact into the tail-shape conversion the assembly needs. Pure $\log$ algebra, no probability.
-- source:
--   Boucheron–Lugosi–Massart, Concentration Inequalities (OUP 2013) §2.7 (Bennett ⇒ Bernstein); Bennett 1962 (JASA 57:33–45); CR2009 §9.1 eq.(9.2).

import Mathlib.Analysis.SpecialFunctions.Log.Basic

theorem talagrand_tangent_sampling_bennett_log_tail_from_bernstein_bridge_dense
    (u : ℝ) :
    0 ≤ u →
    u ^ 2 / (2 + 2 * u / 3) ≤ (1 + u) * Real.log (1 + u) - u := by
  sorry
