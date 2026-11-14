-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_positive_weighted_log
-- name    : ZeroFreeRRG.Hardcore.hardcore_positive_weighted_log
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:59:00.179202+00:00
-- url     : https://prove2.me/theorems/65e443ca-7239-4355-9dc2-72cb469b45f2
-- title:
--   Strict positivity of the hardcore weighted logarithmic expectation
-- statement:
--   Let $d\ge2$, $\theta>0$, and let $X_1,\dots,X_d$ be independent with a bounded nonnegative mean-one law other than $\delta_1$. Then $$\mathbb E\left[\left(\prod_i X_i-\sum_i X_i+d-1\right)\log\left(1+\theta\prod_iX_i\right)\right]>0.$$ This is the strict logarithmic expectation appearing in the hardcore parameter comparison.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, proof of Lemma 4.17, equation (25), pp. 29–31.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.hardcore_positive_weighted_log (d : ℕ) (hd : 2 ≤ d) (θ C : ℝ) (hθ : 0 < θ) (hC : 0 ≤ C)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hbound : ∀ᵐ x ∂μ, 0 ≤ x ∧ x ≤ C)
    (hint : Integrable (fun x : ℝ => x) μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 1) (hne : μ ≠ Measure.dirac 1) :
    0 < ∫ xs : Fin d → ℝ, ((∏ i, xs i) - ∑ i, xs i + d - 1) *
      Real.log (1+θ*∏ i, xs i) ∂(Measure.pi fun _ : Fin d => μ) := by sorry
