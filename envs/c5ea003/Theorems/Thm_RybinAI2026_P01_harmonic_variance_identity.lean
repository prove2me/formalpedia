-- Prove2me | Theorems.Thm_RybinAI2026_P01_harmonic_variance_identity
-- name    : RybinAI2026.P01.harmonic_variance_identity
-- status  : Proved
-- author  : @miao
-- created : 2026-09-10T14:49:36.259643+00:00
-- url     : https://prove2.me/theorems/76b26d3b-d8f3-494a-82e4-03678bb47b0e
-- title:
--   Exact variance slack in the harmonic integral inequality
-- statement:
--   Let $\mu$ be a finite Borel measure on a compact space, let $k$ and $r$ be continuous real functions, and assume $r(x)>0$ everywhere. Then
--
--   $$
--   \left(\int kr\,d\mu\right)\left(\int \frac{k}{r}\,d\mu\right)-\left(\int k\,d\mu\right)^2
--   =\frac12\iint k(x)k(y)\frac{(r(x)-r(y))^2}{r(x)r(y)}\,d\mu(x)\,d\mu(y).
--   $$
--
--   For nonnegative $k$, the right side is the exact nonnegative slack in the Cauchy--Schwarz step underlying harmonic-mean contraction. The identity is useful when a variance-free harmonic bound is too coarse, including in the denominator-addition analysis for Problem 1. No normalization of $\mu$ is assumed.
-- source:
--   Standard polarization/variance identity obtained by expanding the double integral; used here to retain the exact slack in the harmonic denominator estimate derived from https://rybindmitry.github.io/problems/1.html. Not a separately stated theorem in that source.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

theorem RybinAI2026.P01.harmonic_variance_identity
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α]
    [CompactSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (k r : α → ℝ) (hk : Continuous k) (hr : Continuous r)
    (hrpos : ∀ x, 0 < r x) :
    (∫ x, k x*r x ∂μ)*(∫ x, k x/r x ∂μ)-(∫ x, k x ∂μ)^2 =
      (1/2 : ℝ) * ∫ z : α × α,
        k z.1*k z.2*(r z.1-r z.2)^2/(r z.1*r z.2) ∂(μ.prod μ) := by
  sorry
