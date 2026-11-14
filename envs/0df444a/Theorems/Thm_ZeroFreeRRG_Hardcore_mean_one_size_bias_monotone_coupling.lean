-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_mean_one_size_bias_monotone_coupling
-- name    : ZeroFreeRRG.Hardcore.mean_one_size_bias_monotone_coupling
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:21:41.889443+00:00
-- url     : https://prove2.me/theorems/9b87fbd7-ac87-4796-992b-64280735acac
-- title:
--   Monotone coupling with a mean-one size-biased law
-- statement:
--   Let $\mu$ be a probability measure supported on the nonnegative real numbers with finite mean one, and let $\mu^*$ be its size-biased law $d\mu^*(x)=x\,d\mu(x)$. There exists a probability measure $\pi$ on pairs whose first marginal is $\mu$, whose second marginal is $\mu^*$, and for which $x\le y$ almost surely. This constructs the ordered size-bias coupling used in the hardcore part of Lemma 4.17.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, printed p. 30.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

namespace ZeroFreeRRG.Hardcore
theorem mean_one_size_bias_monotone_coupling (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ x ∂μ, 0 ≤ x) (hint : Integrable (fun x => x) μ)
    (hmean : (∫ x, x ∂μ) = 1) :
    ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧
      Measure.map Prod.fst π = μ ∧
      Measure.map Prod.snd π = μ.withDensity (fun x => ENNReal.ofReal x) ∧
      (∀ᵐ p ∂π, p.1 ≤ p.2) := by sorry
end ZeroFreeRRG.Hardcore
