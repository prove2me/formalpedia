-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_gradient_mean_zero
-- name    : ZeroFreeRRG.Hardcore.hardcore_gradient_mean_zero
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:10:15.356997+00:00
-- url     : https://prove2.me/theorems/a8367b61-8205-4bf2-ae40-721b0aa2911e
-- title:
--   The hardcore vertex derivative numerator has mean zero
-- statement:
--   Let $d\ge1$ and let independent $X_i$ have a mean-zero law supported on $[-1,1]$. For any real $\theta$, with $P=\prod_i(1+\theta X_i)$ and $Q=\prod_i(1-X_i)$, the hardcore derivative numerator obeys $$\mathbb E[(1+\theta)P′+Q-P]=0.$$
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, proof of Lemma 4.17, pp. 29–31.

import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.hardcore_gradient_mean_zero (d : ℕ) (hd : 0 < d) (μ : Measure ℝ) [IsProbabilityMeasure μ] (θ : ℝ)
    (hb : ∀ᵐ x ∂μ, -1 ≤ x ∧ x ≤ 1)
    (hint : Integrable (fun x : ℝ => x) μ) (hmean : (∫ x : ℝ, x ∂μ) = 0) :
    (∫ xs : Fin d → ℝ, ((1+θ)*(∑ j, (∏ k ∈ Finset.univ.erase j, (1+θ*xs k))*xs j) +
       (∏ k, (1-xs k)) - ∏ k, (1+θ*xs k)) ∂(Measure.pi fun _ : Fin d => μ)) = 0 := by sorry
