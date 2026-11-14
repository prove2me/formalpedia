-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_gradient_log_product_cancellation
-- name    : ZeroFreeRRG.Hardcore.hardcore_gradient_log_product_cancellation
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:09:45.1352+00:00
-- url     : https://prove2.me/theorems/f58c2d52-8c1c-4728-8033-11af5fb7ba4b
-- title:
--   Cancellation of the log-product term in the hardcore derivative
-- statement:
--   Let $X_1,\ldots,X_d$ be independent from a mean-zero law supported on $[-1,1]$, and let $0\le\theta<1$. Writing $P=\prod_i(1+\theta X_i)$ and $Q=\prod_i(1-X_i)$, the derivative numerator satisfies $$\mathbb E[((1+\theta)P′+Q-P)\log P]=0.$$ The formal statement writes $\log P$ as the sum of the logarithms of its positive factors.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, proof of Lemma 4.17, pp. 29–31.

import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.hardcore_gradient_log_product_cancellation (d : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hb : ∀ᵐ x ∂μ, -1 ≤ x ∧ x ≤ 1)
    (hint : Integrable (fun x : ℝ => x) μ) (hmean : (∫ x : ℝ, x ∂μ) = 0) :
    (∫ xs : Fin d → ℝ, ((1+θ)*(∑ j, (∏ k ∈ Finset.univ.erase j, (1+θ*xs k))*xs j) +
       (∏ k, (1-xs k)) - ∏ k, (1+θ*xs k)) * ∑ i, Real.log (1+θ*xs i)
      ∂(Measure.pi fun _ : Fin d => μ)) = 0 := by sorry
