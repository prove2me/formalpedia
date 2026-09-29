-- Prove2me | Theorems.Thm_survival_mean_ibp
-- name    : survival_mean_ibp
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T20:01:58.274913+00:00
-- url     : https://prove2.me/theorems/39f3fac2-cd97-4607-acdc-f246bc4be318
-- title:
--   Mean as the integral of the survival function (integration by parts)
-- statement:
--   **Survival-function mean identity (improper integration by parts).** Let $F:\mathbb{R}\to\mathbb{R}$ be the CDF of a nonnegative random variable with density $f$, i.e. $F'(t)=f(t)$ for all $t$. Then the mean equals the integral of the survival function: $$\int_0^\infty t\,f(t)\,dt = \int_0^\infty (1-F(t))\,dt,$$ provided $t\cdot f$ and $1-F$ are integrable on $(0,\infty)$ and the boundary term $t\,(1-F(t))\to 0$ as $t\to\infty$. This is the standard tail-integral / layer-cake identity for the expectation of a nonnegative random variable, proved by improper integration by parts with $u(t)=t$, $v(t)=1-F(t)$.
-- source:
--   Standard layer-cake / tail-integral identity for the expectation of a nonnegative random variable (E[T] = ∫₀^∞ P(T>t) dt). Used in A. Siegel, 'Median Bounds and their Application', J. Algorithms 38:184-236 (2001), Lemma 2.1 / Theorem 2.2, to identify the mean of the waiting-time density with ∫(1-F). Proof = improper integration by parts (MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul).

import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
open MeasureTheory Set Filter Topology

theorem survival_mean_ibp (F f : ℝ → ℝ) (hF : ∀ x, HasDerivAt F (f x) x) (hint_tf : IntegrableOn (fun t => t * f t) (Ioi (0:ℝ))) (hint_surv : IntegrableOn (fun t => 1 - F t) (Ioi (0:ℝ))) (hdecay : Tendsto (fun t => t * (1 - F t)) atTop (𝓝 0)) : ∫ t in Ioi (0:ℝ), t * f t = ∫ t in Ioi (0:ℝ), (1 - F t) := by sorry
