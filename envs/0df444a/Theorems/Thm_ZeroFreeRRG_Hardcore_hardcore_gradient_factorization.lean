-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_gradient_factorization
-- name    : ZeroFreeRRG.Hardcore.hardcore_gradient_factorization
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:59:11.789194+00:00
-- url     : https://prove2.me/theorems/481a5ea3-840b-4626-a3d4-132b54562f4e
-- title:
--   Factorization of the hardcore vertex derivative numerator
-- statement:
--   For finitely many real messages $h_i$ and $1+\theta h_i\ne0$, set $P=\prod_i(1+\theta h_i)$, $Q=\prod_i(1-h_i)$ and $W_i=(1-h_i)/(1+\theta h_i)$. The numerator obtained by differentiating the hardcore vertex factor satisfies $$(1+\theta)P′+Q-P=P\left(\prod_iW_i-\sum_iW_i+d-1\right),$$ with $P′$ expanded as a finite sum in the formal statement.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, proof of Lemma 4.17, equation (25), pp. 29–31.

import Mathlib
set_option autoImplicit false
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.hardcore_gradient_factorization (d : ℕ) (h : Fin d → ℝ) (θ : ℝ)
    (hden : ∀ i, 1+θ*h i ≠ 0) :
    let P := ∏ i, (1+θ*h i)
    let Q := ∏ i, (1-h i)
    let W := fun i => (1-h i)/(1+θ*h i)
    (1+θ)*(∑ i, (∏ j ∈ Finset.univ.erase i, (1+θ*h j))*h i) + Q - P =
      P*((∏ i, W i) - ∑ i, W i + d - 1) := by sorry
