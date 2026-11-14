-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_gradient_coordinate_cancellation
-- name    : ZeroFreeRRG.Hardcore.hardcore_gradient_coordinate_cancellation
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:08:36.709243+00:00
-- url     : https://prove2.me/theorems/1055c9ce-f1c6-495a-a446-fa2034fa9fdf
-- title:
--   Mean-zero cancellation of the hardcore derivative against one coordinate
-- statement:
--   For independent mean-zero variables $X_1,\dots,X_d$, the hardcore vertex derivative numerator has zero expectation when multiplied by any integrable test $\varphi(X_i)$, provided the products listed in the formal statement are integrable. Explicitly, if $P=\prod_j(1+\theta X_j)$ and $Q=\prod_j(1-X_j)$, then $$\mathbb E\big[((1+\theta)P′+Q-P)\varphi(X_i)\big]=0.$$
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, proof of Lemma 4.17, pp. 29–31.

import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.hardcore_gradient_coordinate_cancellation (d : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (θ : ℝ)
    (hint : Integrable (fun x : ℝ => x) μ) (hmean : (∫ x : ℝ, x ∂μ) = 0)
    (φ : ℝ → ℝ) (hφ : Integrable φ μ) (hxφ : Integrable (fun x => x*φ x) μ)
    (i : Fin d)
    (hN : ∀ j, Integrable (fun xs : Fin d → ℝ =>
      ((∏ k ∈ Finset.univ.erase j, (1+θ*xs k))*xs j) * φ (xs i))
      (Measure.pi fun _ : Fin d => μ))
    (hP : Integrable (fun xs : Fin d → ℝ => (∏ k, (1+θ*xs k)) * φ (xs i))
      (Measure.pi fun _ : Fin d => μ))
    (hQ : Integrable (fun xs : Fin d → ℝ => (∏ k, (1-xs k)) * φ (xs i))
      (Measure.pi fun _ : Fin d => μ)) :
    (∫ xs : Fin d → ℝ, ((1+θ)*(∑ j, (∏ k ∈ Finset.univ.erase j, (1+θ*xs k))*xs j) +
       (∏ k, (1-xs k)) - ∏ k, (1+θ*xs k))*φ (xs i)
      ∂(Measure.pi fun _ : Fin d => μ)) = 0 := by sorry
