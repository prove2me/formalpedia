-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_tilted_gradient_positive
-- name    : ZeroFreeRRG.Hardcore.hardcore_tilted_gradient_positive
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:02:39.73201+00:00
-- url     : https://prove2.me/theorems/031dff40-1e67-4695-a001-32aa19721626
-- title:
--   Strict positivity of the hardcore tilted gradient term
-- statement:
--   Let $d\ge2$ and let $\eta$ be a mean-zero probability law supported on $[-1,1]$, not concentrated at zero. For $0<\theta<1$, set $W(h)=(1-h)/(1+\theta h)$. The expectation under $d$ independent $\eta$-samples of $$\left(\prod_i(1+\theta h_i)\right)\left(\prod_iW(h_i)-\sum_iW(h_i)+d-1\right)\log\left(1+\theta\prod_iW(h_i)\right)$$ is strictly positive. This is the sign-bearing term in the hardcore vertex derivative.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, proof of Lemma 4.17, equation (25), pp. 29–31.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Classical BigOperators ENNReal

theorem ZeroFreeRRG.Hardcore.hardcore_tilted_gradient_positive (d : ℕ) (hd : 2 ≤ d) (η : Measure ℝ) [IsProbabilityMeasure η]
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hb : ∀ᵐ h ∂η, -1 ≤ h ∧ h ≤ 1)
    (hint : Integrable (fun h : ℝ => h) η)
    (hmean : (∫ h : ℝ, h ∂η) = 0)
    (hn : ¬(∀ᵐ h ∂η, h = 0)) :
    let W := fun h : ℝ => (1-h)/(1+θ*h)
    0 < ∫ hs : Fin d → ℝ, (∏ i, (1+θ*hs i)) *
      (((∏ i, W (hs i)) - ∑ i, W (hs i) + d - 1) *
        Real.log (1+θ*∏ i, W (hs i))) ∂(Measure.pi fun _ : Fin d => η) := by sorry
